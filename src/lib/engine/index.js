'use strict';

Object.defineProperty(exports, "__esModule", {
    value: true
});

var _extends = Object.assign || function (target) { for (var i = 1; i < arguments.length; i++) { var source = arguments[i]; for (var key in source) { if (Object.prototype.hasOwnProperty.call(source, key)) { target[key] = source[key]; } } } return target; };

/* eslint-disable */
/*
 * Copyright (c) 2017-present, Block Collider developers, All rights reserved.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * 
 */

console.warn = () => {};
/* eslint-enable */

const debug = require('debug')('bcnode:engine');
const crypto = require('crypto');

const { EventEmitter } = require('events');
const { join, resolve } = require('path');
const { writeFileSync } = require('fs');
const { max } = require('ramda');
const { queue } = require('async');
const maxmind = require('maxmind');
const LRUCache = require('lru-cache');
const BN = require('bn.js');
const semver = require('semver');
const fkill = require('fkill');
const { config } = require('../config');
const { ensureDebugPath } = require('../debug');
const { Multiverse } = require('../bc/multiverse');
const { getLogger } = require('../logger');
const { Monitor } = require('../monitor');
const { Node } = require('../p2p');
const { RoverManager } = require('../rover/manager');
const rovers = require('../rover/manager').rovers;
const { Server } = require('../server/index');
const PersistenceRocksDb = require('../persistence').RocksDb;
const { PubSub } = require('./pubsub');
const { RpcServer } = require('../rpc/index');
const { getGenesisBlock } = require('../bc/genesis');
const { getBootBlock } = require('../bc/bootblock');
const { BlockPool } = require('../bc/blockpool');
const { isValidBlockCached, validateSequenceDifficulty } = require('../bc/validation');
const { Block } = require('../protos/core_pb');
const { errToString } = require('../helper/error');
const { getVersion } = require('../helper/version');
const { MiningOfficer } = require('../mining/officer');
const { WorkerPool } = require('../mining/pool');
const ts = require('../utils/time').default; // ES6 default export

const GEO_DB_PATH = resolve(__dirname, '..', '..', 'data', 'GeoLite2-City.mmdb');

const DATA_DIR = process.env.BC_DATA_DIR || config.persistence.path;
const MONITOR_ENABLED = process.env.BC_MONITOR === 'true';
const BC_CHECK = process.env.BC_CHECK === 'true';
const PERSIST_ROVER_DATA = process.env.PERSIST_ROVER_DATA === 'true';
const BC_BT_VALIDATION = process.env.BC_BT_VALIDATION === 'true';
const BC_REMOVE_BTC = process.env.BC_REMOVE_BTC === 'true';

process.on('uncaughtError', err => {
    /* eslint-disable */
    console.trace(err);
    /* eslint-enable */
    process.exit(3);
});

/* eslint-disable */
class Engine {
    // TODO only needed because of server touches that - should be passed using constructor?
    constructor(opts) {
        this._logger = getLogger(__filename);
        this._knownRovers = opts.rovers;
        this._minerKey = opts.minerKey; // TODO only needed because of server touches that - should be passed using constructor?
        this._rawBlock = [];
        this._blockCache = [];
        this._monitor = new Monitor(this, {});
        this._persistence = new PersistenceRocksDb(DATA_DIR);
        this._pubsub = new PubSub();
        this._node = new Node(this);
        this._rovers = new RoverManager();
        this._emitter = new EventEmitter();
        this._rpc = new RpcServer(this);
        this._server = new Server(this, this._rpc);
        this._subscribers = {};
        this._verses = [];
        this._stepSyncTimestamps = [];
        this._server.count = 0;
        this._storageQueue = queue((fn, cb) => {
            return fn.then(res => {
                cb(null, res);
            }).catch(err => {
                cb(err);
            });
        });

        // Open Maxmind Geo DB
        this._geoDb = maxmind.openSync(GEO_DB_PATH);

        process.on('uncaughtError', function (err) {
            this._logger.error(err);
        });

        this._knownEvaluationsCache = LRUCache({
            max: config.engine.knownBlocksCache.max
        });

        this._knownBlocksCache = LRUCache({
            max: config.engine.knownBlocksCache.max
        });

        this._rawBlocks = LRUCache({
            max: config.engine.rawBlocksCache.max
        });

        this._peerIsSyncing = false;
        this._peerIsResyncing = false;

        // Start NTP sync
        ts.start();
    }

    get geoDb() {
        return this._geoDb;
    }

    // TODO only needed because of server touches that - should be passed using constructor?
    get minerKey() {
        return this._minerKey;
    }

    /**
     * Get WorkerPool
     * @returns {WorkerPool|*}
     */
    get workerPool() {
        return this._workerPool;
    }

    /**
     * Get multiverse
     * @returns {Multiverse|*}
     */
    get multiverse() {
        return this.node.multiverse;
    }

    set multiverse(multiverse) {
        this.node.multiverse = multiverse;
    }

    /**
     * Get blockpool
     * @returns {BlockPool|*}
     */
    get blockpool() {
        return this.node.blockpool;
    }

    /**
     * Get pubsub wrapper instance
     * @returns {PubSub}
     */
    get pubsub() {
        return this._pubsub;
    }

    /**
     * Initialize engine internals
     *
     * - Open database
     * - Store name of available rovers
     */
    async init() {
        const roverNames = Object.keys(rovers);
        const {
            npm,
            git: {
                long
            }
        } = getVersion();
        const newGenesisBlock = getGenesisBlock();
        const versionData = {
            version: npm,
            commit: long,
            db_version: 1
        };
        const engineQueue = queue((fn, cb) => {
            return fn.then(res => {
                cb(null, res);
            }).catch(err => {
                cb(err);
            });
        });
        const DB_LOCATION = resolve(`${__dirname}/../../${this.persistence._db.location}`);
        const DELETE_MESSAGE = `DB data structure is stale, delete data folder '${DB_LOCATION}' and run bcnode again`;
        // TODO get from CLI / config
        try {
            await this._persistence.open();
            try {
                let version = await this.persistence.get('appversion');
                if (semver.lt(version.version, '0.7.7')) {
                    // GENESIS BLOCK 0.9
                    this._logger.warn(DELETE_MESSAGE);
                    process.exit(8);
                }
            } catch (_) {
                // silently continue - the version is not present so
                // a) very old db
                // b) user just remove database so let's store it
            }
            let res = await this.persistence.put('rovers', roverNames);
            if (res) {
                this._logger.info('stored rovers to persistence');
            }
            res = await this.persistence.put('appversion', versionData);
            if (res) {
                this._logger.info('stored appversion to persistence');
            }

            if (BC_REMOVE_BTC === true) {
                this._logger.warn('REMOVE BTC BLOCK LATEST FLAG TRIGGERED');
                await this.persistence.del('btc.block.latest');
                await this.persistence.del('btc.block.546785');
                await this.persistence.del('btc.block.546784');
                await this.persistence.del('btc.block.546783');
            }
            /* eslint-disable */
            try {
                const latestBlock = await this.persistence.get('bc.block.latest');
                await this.multiverse.addNextBlock(latestBlock);
                await this.persistence.put('synclock', newGenesisBlock);
                await this.persistence.put('bc.block.oldest', newGenesisBlock);
                await this.persistence.put('bc.block.parent', newGenesisBlock);
                await this.persistence.get('bc.block.1');
                await this.persistence.put('bc.dht.quorum', '0');
                /* eslint-disable */
            } catch (_) {
                // genesis block not found
                try {
                    await this.persistence.put('synclock', newGenesisBlock);
                    await this.persistence.put('bc.block.1', newGenesisBlock);
                    await this.persistence.put('bc.block.latest', newGenesisBlock);
                    await this.persistence.put('bc.block.parent', newGenesisBlock);
                    await this.persistence.put('bc.block.oldest', newGenesisBlock);
                    await this.persistence.put('bc.block.checkpoint', newGenesisBlock);
                    await this.persistence.put('bc.dht.quorum', '0');
                    await this.persistence.put('bc.depth', 2);
                    await this.multiverse.addNextBlock(newGenesisBlock);
                    this._logger.info('genesis block saved to disk ' + newGenesisBlock.getHash());
                } catch (e) {
                    this._logger.error(`error while creating genesis block ${e.message}`);
                    process.exit(1);
                }
            }
            if (process.env.BC_BOOT_BLOCK !== undefined) {
                const bootBlock = getBootBlock(process.env.BC_BOOT_BLOCK);
                await this.persistence.put('bc.block.latest', bootBlock);
                await this.persistence.put('bc.block.' + bootBlock.getHeight(), bootBlock);
                await this.multiverse._chain.unshift(bootBlock);
                this._logger.warn('boot block ' + bootBlock.getHeight() + ' assigned as latest block');
            }
        } catch (e) {
            this._logger.warn(`could not store rovers to persistence, reason ${e.message}`);
        }

        if (BC_CHECK === true) {
            await this.integrityCheck();
        }

        if (MONITOR_ENABLED) {
            this._monitor.start();
        }

        this.pubsub.subscribe('state.block.height', '<engine>', msg => {
            this.storeHeight(msg).then(res => {
                if (res === true) {
                    this._logger.info('wrote block ' + msg.data.getHeight());
                }
            }).catch(err => {
                this._logger.error(errToString(err));
            });
        });

        this.pubsub.subscribe('update.checkpoint.start', '<engine>', msg => {
            this._peerIsResyncing = true;
        });

        this.pubsub.subscribe('update.mined.block', '<engine>', msg => {
            this._logger.info('------ update.mined.block -----');
        });

        this.pubsub.subscribe('state.resync.failed', '<engine>', msg => {
            this._logger.info('pausing mining to reestablish multiverse');
            this._peerIsResyncing = true;
            engineQueue.push(this.blockpool.purge(msg.data), err => {
                if (err) {
                    this._logger.error(`Queued task failed, reason: ${err.message}`);
                }
            });
        });

        //[this.pubsub.subscribe('miner.block.new', (msg) => {
        //[		/* eslint-disable */
        //[		console.log('miner.block.new -----------> ')
        //[		console.log(msg)
        //[})

        //this.pubsub.subscribe('mined', (msg) => {
        //		/* eslint-disable */
        //		console.log('miner -----------> ')
        //		console.log(msg)
        //})

        this.pubsub.subscribe('state.checkpoint.end', '<engine>', msg => {
            this._peerIsResyncing = false;
        });

        this.pubsub.subscribe('update.block.latest', '<engine>', msg => {
            try {
                if (!this._knownEvaluationsCache.has(msg.data.getHash())) {
                    this._knownEvaluationsCache.set(msg.data.getHash(), 1);
                    // TODO: Check if any blocks are not the current one and reuse if its new
                    // this could be rebase
                    // this.miningOfficer.stopMining(this._workerPool)
                    this.updateLatestAndStore(msg).then(previousBlock => {
                        if (msg.mined !== undefined && msg.mined === true) {
                            this._logger.info(`latest block ${msg.data.getHeight()} has been updated`);
                        } else {
                            // this.miningOfficer.rebaseMiner()
                            // .then((state) => {
                            //   this._logger.info(`latest block ${msg.data.getHeight()} has been updated`)
                            // })
                            // .catch((err) => {
                            //   this._logger.error(`error occurred during updateLatestAndStore(), reason: ${err.message}`)
                            // })
                        }
                        this._blockCache.length = 0;
                        //if(this._blockCache.length > 0){
                        //    const candidates = this._blockCache.reduce((all, block) => {
                        //      const blockchains = previousBlock.getBlockchainHeaders().toObject()
                        //      const key = block.getBlockchain() + 'List'
                        //      const headers = blockchains[key]
                        //      const found = headers.reduce((f, header) => {
                        //         if(all === false) {
                        //           if(block.getHeight() > header.getHeight()){
                        //              f = true
                        //           }
                        //         }
                        //         return f
                        //      }, false)

                        //      if(found === true) {
                        //        all.push(block)
                        //      }
                        //      return all
                        //    }, [])
                        //    this._blockCache.length = 0
                        //    if(candidates.length > 0){
                        //      this._blockCache = candidates
                        //      const nextBlock = this._blockCache.shift()
                        //      this.miningOfficer.newRoveredBlock(rovers, nextBlock, this._blockCache)
                        //        .then((pid: number | false) => {
                        //            if (pid !== false) {
                        //                this._logger.info(`collectBlock handler: sent to miner`)
                        //            }
                        //        })
                        //        .catch(err => {
                        //            this._logger.error(`could not send to mining worker, reason: ${errToString(err)}`)
                        //            process.exit()
                        //        })

                        //    }
                        //}
                    }).catch(err => {
                        this._logger.info(errToString(err));
                        this._logger.error(`error occurred during updateLatestAndStore(), reason: ${err.message}`);
                        process.exit();
                    });
                }
            } catch (err) {
                this._logger.error(err);
            }
        });

        // GENERATE BLOCKS - BEGIN

        const BC_PLUGIN = process.env.BC_PLUGIN;
        if (BC_PLUGIN) {
            const pluginPath = resolve(join(__dirname, '..', '..', BC_PLUGIN));

            try {
                const plugin = require(pluginPath);
                await plugin.main(this);
            } catch (err) {
                this._logger.error('PLUGIN ERROR', err);
                this._logger.error(err);
            }
        }

        this.pubsub.subscribe('miner.block.new', '<engine>', ({
            unfinishedBlock,
            solution
        }) => {
            return this._processMinedBlock(unfinishedBlock, solution).then(res => {
                if (res === true) {
                    return this._broadcastMinedBlock(unfinishedBlock, solution).then(res => {
                        this._logger.info('broadcasted mined block', res);
                    }).catch(err => {
                        this._logger.error(`mined block broadcast failed -> ${err.message}`);
                    });
                }
            }).catch(err => {
                this._logger.warn(err);
            });
        });

        this._workerPool = new WorkerPool(this._pubsub, this._persistence, {
            minerKey: this._minerKey
        });

        this._miningOfficer = new MiningOfficer(this._pubsub, this._persistence, this._workerPool, {
            minerKey: this._minerKey,
            rovers: this._knownRovers
        });

        this._workerPool.emitter.on('mined', data => {
            //this.miningOfficer.stopMining()
            fkill('bcworker', { force: true }).then(() => {
                this._logger.info('workers dismissed');
            }).catch(err => {
                this._logger.debug(err);
            });
            this.miningOfficer._handleWorkerFinishedMessage(data);
        });

        this._workerPool.emitter.on('blockCacheRebase', () => {
            this._logger.info('block cache rebase requested');
            this.persistence.get('bc.block.latest').then(previousBlock => {
                if (this._blockCache.length > 0) {
                    const candidates = this._blockCache.reduce((all, block) => {
                        const blockchains = previousBlock.getBlockchainHeaders().toObject();
                        const key = block.getBlockchain() + 'List';
                        const headers = blockchains[key];
                        const found = headers.reduce((f, header) => {
                            if (all === false) {
                                if (block.getHeight() > header.getHeight()) {
                                    f = true;
                                }
                            }
                            return f;
                        }, false);

                        if (found === true) {
                            all.push(block);
                        }
                        return all;
                    }, []);
                    this._blockCache.length = 0;
                    if (candidates.length > 0) {
                        this._blockCache = candidates;
                        const nextBlock = this._blockCache.shift();
                        this.miningOfficer.newRoveredBlock(rovers, nextBlock, this._blockCache).then(pid => {
                            if (pid !== false) {
                                this._logger.info(`collectBlock reassigned sent to miner`);
                            }
                        }).catch(err => {
                            this._logger.error(`could not send to mining worker, reason: ${errToString(err)}`);
                            process.exit();
                        });
                    }
                }
            }).catch(err => {
                this._logger.debug(err);
            });
        });
        await this._miningOfficer.simMining();
    }

    /**
     * Store a block in persistence unless its Genesis Block
     * @returns Promise
        ehs._logger.info('pmb' + 4)
     */
    async storeHeight(msg) {
        const block = msg.data;
        // Block is genesis block
        if (block.getHeight() < 2) {
            return;
        }
        if (msg.force !== undefined && msg.force === true) {
            try {
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                return Promise.resolve(block);
            } catch (err) {
                this._logger.warn('unable to store block ' + block.getHeight() + ' - ' + block.getHash());
                return Promise.reject(err);
            }
        } else {
            try {
                let prev = getGenesisBlock();
                if (block.getHeight() - 1 > 0) {
                    prev = await this.persistence.get('bc.block.' + (block.getHeight() - 1));
                }
                if (prev.getHash() === block.getPreviousHash() && new BN(prev.getTotalDistance()).lt(new BN(block.getTotalDistance()) === true)) {
                    await this.persistence.put('bc.block.' + block.getHeight(), block);
                    return Promise.resolve(true);
                } else {
                    return Promise.reject(new Error('block state did not match'));
                }
            } catch (err) {
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                this._logger.warn(' stored orphan ' + block.getHeight() + ' - ' + block.getHash());
                return Promise.resolve(true);
            }
        }
    }

    /**
     * Store a block in persistence unless its Genesis Block
     * @returns Promise
     */
    async updateLatestAndStore(msg) {
        const block = msg.data;
        let storeChildHeaders = {
            btc: false,
            neo: false,
            lsk: true,
            eth: false,
            wav: false
        };
        if (msg.childHeaders !== undefined) {
            storeChildHeaders = msg.childHeaders;
        }
        // override all settings if validation mode is strict
        if (BC_BT_VALIDATION === true) {
            storeChildHeaders = {
                btc: false,
                neo: false,
                lsk: false,
                eth: true,
                wav: false
            };
        }
        this._logger.info('store block: ' + block.getHeight() + ' ' + block.getHash());
        try {
            const previousLatest = await this.persistence.get('bc.block.latest');
            const parent = await this.persistence.get('bc.block.parent');
            const synclock = await this.persistence.get('synclock');

            // check if there is a decision tree cycle required
            if (parent.getHash() !== previousLatest.getPreviousHash() && new BN(block.getTotalDistance()).gt(new BN(previousLatest.getTotalDistance())) && new BN(block.getTimestamp()).gte(new BN(previousLatest.getTimestamp()))) {
                // reset to previousLatestPath
                // behavior must be echoed in multiverse
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else if (previousLatest.getHash() === block.getPreviousHash() && new BN(block.getTimestamp()).gt(new BN(parent.getTimestamp())) === true && validateSequenceDifficulty(previousLatest, block) === true) {
                await this.persistence.put('bc.block.parent', previousLatest);
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else if (previousLatest.getHeight() === 1) {
                await this.persistence.put('bc.block.parent', previousLatest);
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else if (msg.force === true && msg.multiverse !== undefined && msg.multiverse.constructor === Array.constructor && synclock.getHeight() === 1) {
                const oldest = msg.multiverse[msg.multiverse - 1];
                // get the block before the oldest available block
                const grandparent = await this.persistence.get('bc.block.' + oldest.getHeight() - 1);
                if (oldest.getPreviousHash() !== grandparent.getHash()) {
                    // this is a new chain branch and we must sync for it
                    await this.persistence.put('synclock', oldest);
                }
                await this.persistence.put('bc.block.parent', msg.multiverse[1]);
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
                /*
                 * Remove this after block 100,000
                 */
            } else if (msg.force === true && synclock.getHeight() === 1) {
                await this.persistence.put('synclock', block);
                // here we set it up so that on the next cycle we can compare paths
                await this.persistence.put('bc.block.parent', previousLatest);
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else if (parent.getHash() === block.getPreviousHash()) {
                await this.persistence.put('bc.block.parent', msg.multiverse[1]);
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else {
                this._logger.error('failed to set block ' + block.getHeight() + ' ' + block.getHash() + ' as latest block <- invalid chain');
            }

            if (msg.multiverse !== undefined) {
                while (msg.multiverse.length > 0) {
                    const b = msg.multiverse.pop();
                    // strict local only write of genesis block
                    if (b.getHeight() > 1) {
                        await this.persistence.put('bc.block.' + b.getHeight(), b);
                        await this.persistence.putChildHeaders(b, storeChildHeaders);
                    }
                }
                return Promise.resolve(block);
            }

            if (this.miningOfficer._canMine === false) {
                this._logger.info('determining if rovered headers include new child blocks');
                const latestRoveredHeadersKeys = this.miningOfficer._knownRovers.map(chain => `${chain}.block.latest`);
                const latestBlockHeaders = await this.persistence.getBulk(latestRoveredHeadersKeys);
                latestBlockHeaders.map(r => {
                    if (this.miningOfficer._collectedBlocks[r.getBlockchain()] < 1) {
                        this.miningOfficer._collectedBlocks[r.getBlockchain()]++;
                    }
                });
            }
            return Promise.resolve(block);
        } catch (err) {
            this._logger.warn(err);
            this._logger.error(errToString(err));
            this._logger.warn('no previous block found');
            if (block !== undefined && msg.force === true) {
                await this.persistence.put('bc.block.parent', getGenesisBlock());
                await this.persistence.put('bc.block.latest', block);
                await this.persistence.put('bc.block.' + block.getHeight(), block);
                await this.persistence.putChildHeaders(block, storeChildHeaders);
            } else {
                this._logger.warn('submitted block ' + block.getHeight() + ' ' + block.getHash() + ' will not be persisted');
            }
            if (msg.multiverse !== undefined) {
                // assert the valid state of the entire sequence of each rovered chain
                // DISABLED for BT: const multiverseIsValid = this.miningOfficer.validateRoveredSequences(msg.multiverse)
                while (msg.multiverse.length > 0) {
                    const b = msg.multiverse.pop();
                    if (b.getHeight() > 1) {
                        await this.persistence.put('bc.block.' + b.getHeight(), b);
                        await this.persistence.putChildHeaders(b, storeChildHeaders);
                    }
                }
                return Promise.resolve(block);
            }
            return Promise.resolve(block);
        }
    }

    /**
     * Get node
     * @return {Node}
     */
    get node() {
        return this._node;
    }

    /**
     * Get rawBlock
     * @return {Object}
     */
    get rawBlock() {
        return this._rawBlock;
    }

    /**
     * Set rawBlock
     * @param block
     */
    set rawBlock(block) {
        this._rawBlock = block;
    }

    /**
     * Get persistence
     * @return {Persistence}
     */
    get persistence() {
        return this._persistence;
    }

    /**
     * Get rovers manager
     * @returns RoverManager
     */
    get rovers() {
        return this._rovers;
    }

    /**
     * Get instance of RpcServer
     * @returns RpcServer
     */
    get rpc() {
        return this._rpc;
    }

    /**
     * Get instance of Server (Express on steroids)
     * @returns Server
     */
    get server() {
        return this._server;
    }

    get miningOfficer() {
        return this._miningOfficer;
    }

    /**
     * Start Server
     */
    async startNode() {
        this._logger.info('starting P2P node');
        let nodeId;
        try {
            this._logger.info('loading network key');
            const now = Math.floor(Date.now() * 0.001);
            const nodeObjectData = await this.persistence.get('bc.dht.id');
            const nodeObject = JSON.parse(nodeObjectData);
            nodeId = nodeObject.id;
            this._logger.info('network dht creation timestamp ' + nodeObject.timestamp);
            const nodeTimestamp = nodeObject.timestamp;

            // if the key is more than 1 week old reset it
            if (nodeTimestamp + 604800 < now) {
                this._logger.warn('key needs to be set');
                nodeId = crypto.createHash('sha1').update(crypto.randomBytes(32).toString('hex')).digest('hex');
                this._logger.info('asssigned node ID <- ' + nodeId);
                await this.persistence.put('bc.dht.id', JSON.stringify({
                    id: nodeId,
                    timestamp: Math.floor(Date.now() * 0.001)
                }));
            }
        } catch (_) {
            this._logger.warn('key needs to be set');
            nodeId = crypto.createHash('sha1').update(crypto.randomBytes(32).toString('hex')).digest('hex');
            this._logger.info('asssigned node key <- ' + nodeId);
            await this.persistence.put('bc.dht.id', JSON.stringify({
                id: nodeId,
                timestamp: Math.floor(Date.now() * 0.001)
            }));
        }

        this._emitter.on('peerCount', count => {
            if (this._server) {
                this._server._wsBroadcastPeerConnected(count);
            }
        });

        this._emitter.on('peerConnected', ({
            peer
        }) => {
            if (this._server) {
                this._server._wsBroadcastPeerConnected(peer);
            }
        });

        this._emitter.on('peerDisconnected', ({
            peer
        }) => {
            if (this._server) {
                this._server._wsBroadcastPeerDisonnected(peer);
            }
        });
        return this.node.start(nodeId);
    }

    /**
     * Start rovers
     * @param rovers - list (string; comma-delimited) of rover names to start
     */
    startRovers(rovers) {
        this._logger.info(`starting rovers '${rovers.join(',')}'`);

        rovers.forEach(name => {
            if (name) {
                this._rovers.startRover(name);
            }
        });

        //if (Object.keys(this._workerPool._workers).length === 0) {
        //}

        this.workerPool.allRise().then(() => {
            this._emitter.on('collectBlock', ({
                block
            }) => {
                // Persist block if needed
                if (PERSIST_ROVER_DATA === true) {
                    this._writeRoverData(block);
                }

                process.nextTick(() => {
                    this.miningOfficer.newRoveredBlock(rovers, block, this._blockCache).then(pid => {
                        if (pid !== false) {
                            this._logger.info(`collectBlock handler: sent to miner`);
                        }
                    }).catch(err => {
                        this._logger.error(`could not send to mining worker, reason: ${errToString(err)}`);
                        process.exit();
                    });
                });
            });
        }).catch(err => {
            this._logger.error(err);
            this._logger.error('critical error required application close');
            process.exit(3);
        });
    }

    async integrityCheck() {
        try {
            await this.persistence.get('bc.block.1');
            this._logger.info('chain integrity check running');
            const limit = await this.persistence.stepFrom('bc.block', 1);
            this._logger.info('chain integrity: ' + limit);
            await this.persistence.flushFrom('bc.block', limit);
            return Promise.resolve(limit);
        } catch (err) {
            this._logger.error(err);
            this._logger.warn('unable to use default for integrity check');
            try {
                await this.persistence.set('bc.block.1', getGenesisBlock);
                await this.persistence.flushFrom('bc.block', 1);
            } catch (err) {
                this._logger.error(err);
            }
            return Promise.resolve(1);
        }
    }

    async sendPeerLatestBlock(conn, newBlock) {
        return conn.getPeerInfo((err, peerInfo) => {
            if (err) {
                this._logger.error(errToString(err));
                return Promise.reject(err);
            }

            try {
                const targetPeer = peerInfo.id.toB58String();
                return this.node.sendBlockToPeer(newBlock, targetPeer);
            } catch (err) {
                return Promise.reject(err);
            }
            // request proof of the multiverse from the peer
        });
    }

    /**
     * Takes a range of blocks and validates them against within the contents of a parent and child
     * TODO: Move this to a better location
     * @param blocks BcBlock[]
     */
    async syncSetBlocksInline(blocks, blockKey) {
        let valid = true;
        if (blocks.length < 100) {
            valid = await this.multiverse.validateBlockSequenceInline(blocks);
        }
        if (valid === false) {
            return Promise.reject(new Error('invalid sequence of blocks')); // Enabled after target
        }
        let tasks = [];
        if (blockKey === undefined) {
            tasks = blocks.map(item => this.persistence.put('bc.block.' + item.getHeight(), item));
        } else {
            tasks = blocks.map(item => this.persistence.put(blockKey + '.bc.block.' + item.getHeight(), item));
        }
        await Promise.all(tasks);
        return Promise.resolve(tasks.length);
    }

    /**
     * Determine if a sync request should be made to get the block
     * TODO: Move this to P2P / better location
     * @param conn Connection the block was received from
     * @param newBlock Block itself
     */
    async proveTwo(conn, newBlock) {
        // disabled until
        try {
            this._logger.info('sync from depth start');
            const depthData = await this.persistence.get('bc.depth');
            const depth = parseInt(depthData, 10); // coerce for Flow
            // const checkpoint = await this.persistence.get('bc.block.checkpoint')
            // where the bottom of the chain is
            // if the last height was not a genesis block and the depth was 2 then sync only to the height
            if (depth === 2) {
                // chain has be sequenced backwards until block of height 2
                this._logger.info('depth is 2: sync from depth end');
                return Promise.resolve(true);
                // return Promise.resolve(true)
            } else {
                const upperBound = max(depth, 2) + 1; // so we dont get the genesis block
                const lowBound = max(depth - 1000, 2); // Assigned during AT
                return conn.getPeerInfo((err, peerInfo) => {
                    if (err) {
                        return Promise.reject(err);
                    }
                    return (async () => {
                        const peerLockKey = 'bc.peer.' + peerInfo.id.toB58String();
                        let peerLock = 1; // assume peer is busy
                        try {
                            peerLock = await this.persistence.get(peerLockKey);
                        } catch (err) {
                            // the lock does not exist
                            peerLock = 0;
                        }
                        if (peerLock === 1) {
                            // dont send request because the peer is busy
                            return Promise.resolve(true);
                        } else {
                            // request a range from the peer
                            await this.persistence.put(peerLockKey, 1);
                            // lock the depth for if another block comes while running this
                            await this.persistence.put('bc.depth', upperBound);
                            const query = {
                                queryHash: newBlock.getHash(),
                                queryHeight: newBlock.getHeight(),
                                low: lowBound,
                                high: upperBound
                            };
                            return this.node.manager.createPeer(peerInfo).query(query).then(blocks => {
                                this._logger.info(blocks.length + ' recieved');
                                return this.syncSetBlocksInline(blocks, 'pending').then(blocksStoredResults => {
                                    // if we didn't get the one block above the genesis block run again

                                    /*
                                     * test if it connects to the previous synced chain
                                     * this would happen if a peer disconnected from the node
                                     * and was now resyncing
                                     */
                                    // all done, no more depth clean up, unlock peer
                                    return this.persistence.put(peerLockKey, 0).then(() => {
                                        return this.persistence.put('bc.depth', 2).then(() => {
                                            return this.persistence.putPending('bc');
                                        }).catch(e => {
                                            return Promise.reject(e);
                                        });
                                    }).catch(e => {
                                        this._logger.error(errToString(e));
                                        return Promise.reject(e);
                                    });
                                }).catch(e => {
                                    this._logger.info('error has occured reading bounds');
                                    this._logger.error(errToString(e));
                                    // unlock the peer
                                    return this.persistence.put(peerLockKey, 0).then(() => {
                                        return this.persistence.put('bc.depth', depth).then(() => {
                                            return Promise.resolve(false);
                                        });
                                    }).catch(e => {
                                        // reset the depth
                                        return this.persistence.put('bc.depth', depth).then(() => {
                                            return Promise.reject(e);
                                        });
                                    });
                                });
                            }).catch(e => {
                                // unlock the peer and reset the depth
                                return this.persistence.put(peerLockKey, 0).then(() => {
                                    return this.persistence.put('bc.depth', depth).then(() => {
                                        return Promise.resolve(depth);
                                    });
                                });
                            });
                        }
                    })();
                });
            }
        } catch (err) {
            // no depth has been set
            return Promise.reject(err);
        }
    }

    async stepSyncHandler(msg) {
        let cancelSync = false;
        const now = Math.floor(Date.now() * 0.001);
        const data = msg.data;
        const obj = {
            connction: msg.connection

            // sync is complete emit event
        };if (data.low.getHeight() < 3) {
            this._emitter.emit('synccomplete', true);
            this._stepSyncTimestamps.length = 0;
            await this.persistence.put('synclock', getGenesisBlock());
            return;
        }

        let previousTimestamp = now;
        if (this._stepSyncTimestamps.length > 0) {
            previousTimestamp = this._stepSyncTimestamps[this._stepSyncTimestamps.length - 1];
        }

        this._logger.info('sync request returned from peer in ' + (now - previousTimestamp) + ' seconds');
        await this.persistence.put('synclock', data.low);

        const high = max(3, data.low.getHeight());
        const low = max(2, high - 500);
        obj.data = {
            low: low,
            high: high
        };
        if (cancelSync === false) {
            this._emitter.emit('getblocklist', obj);
        }
    }

    stepSync(conn, height, syncBlockHash) {
        this._logger.info('step sync from height: ' + height);
        // return new Promise(resolve, reject) {
        // check if peer is known to be slow
        return this.persistence.get('synclock').then(syncBlock => {
            if (syncBlock.getHash() !== syncBlockHash) {
                // Another sync override --> break step
                this._logger.warn('previous step sync canceled <- mismatched sync lock hash');
                return Promise.resolve(false);
            }

            if (height < 3) {
                return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                    this._logger.info('sync reset');
                });
            }

            return conn.getPeerInfo((err, peerInfo) => {
                if (err) {
                    this._logger.error(err);
                    return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                        this._logger.info('sync reset');
                    });
                } else {
                    // check if peer is known to have been slow with event type 2
                    if (this.node.manager.getPeerEvent(peerInfo.id.toB58String(), 2) > 0) {
                        return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                            this._logger.info('sync reset');
                            return Promise.resolve(true);
                        }).catch(e => {
                            this._logger.error(e);
                            return Promise.resolve(false);
                        });
                    }

                    if (syncBlock.getHeight() !== 1 && syncBlock.getHash() === syncBlockHash) {
                        const low = max(height - 2500, 2);
                        const query = {
                            queryHash: '0000',
                            queryHeight: height,
                            low: low,
                            high: height
                        };
                        return this.node.manager.createPeer(peerInfo).query(query).then(newBlocks => {
                            this._logger.info(newBlocks.length + ' recieved');
                            return this.syncSetBlocksInline(newBlocks).then(blocksStoredResults => {
                                const lowest = newBlocks[0];
                                return this.persistence.put('bc.block.oldest', lowest).then(() => {
                                    return this.stepSync(conn, low, syncBlockHash);
                                });
                            }).catch(err => {
                                this._logger.warn('sync failed');
                                this._logger.error(err);
                                this.node.manager.putPeerEvent(peerInfo.id.toB58String(), 2);
                                return Promise.resolve(false);
                            });
                        }).catch(e => {
                            this._logger.warn('sync failed');
                            this._logger.error(e);
                            this.node.manager.putPeerEvent(peerInfo.id.toB58String(), 2);
                            return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                                this._logger.info('sync reset');
                                return Promise.resolve(true);
                            });
                        });
                    } else {
                        this._logger.warn('sync canceled');
                        return Promise.resolve(true);
                    }
                }
            });
        }).catch(e => {
            this._logger.warn('sync failed');
            this._logger.error(e);
            return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                this._logger.info('sync reset');
            });
        });
    }

    /**
     * New block received from peer handler
     * @param conn Connection the block was received from
     * @param newBlock Block itself
     */
    blockFromPeer(conn, newBlock) {
        // Test if new block has been seen before
        if (newBlock && !this._knownBlocksCache.get(newBlock.getHash())) {
            // Add block to LRU cache to avoid processing the same block twice
            debug(`Adding received block into cache of known blocks - ${newBlock.getHash()}`);
            this._knownBlocksCache.set(newBlock.getHash(), 1);
            this._logger.info('received new block from peer', newBlock.getHeight());

            // EVAL NEXT
            // is newBlock next after currentHighestBlock? (all)
            // [] - newBlock previousHash is hash of currentHighestBlock
            // [] - newBlock timestamp > currentHighestBlock timestamp
            // [] - newBlock totalDifficulty > currentHighestBlock totalDifficulty
            // [] - newBlock connected chain heights > currentHighestBlock connected chain heights

            // 1 EVAL REJECT / RESYNC
            // * requires currentParentHighestBlock
            // when does newBlock trigger resync after multiverse rejection (pick any)
            // [] = newBlock has greater totalDifficulty
            // [] = greater child heights of the parentHighestBlock
            //
            // 2 EVAL REJECT / RESYNC
            // when no parentBlockExists (light client / early sync)
            // [] = newBlock has greater totalDifficulty
            //
            // after target adds weighted fusion positioning to also evaluate block  -> (X1,Y1) = D1/D1 + D2 * (X1,Y1) + D2 / D1 + D2 * (X2, Y2)
            // encourages grouped transactions from one tower to be more likely to enter a winning block in batch due to lowest distance
            //
            isValidBlockCached(this.persistence, newBlock, 1).then(valid => {
                if (valid === true) {

                    this._logger.info('purposed block peer ' + newBlock.getHeight());
                    return this.multiverse.addNextBlock(newBlock).then(isNextBlock => {
                        if (isNextBlock === true) {

                            let options = {
                                key: 'bc.block.latest',
                                data: newBlock,
                                childHeaders: {
                                    btc: true,
                                    eth: true,
                                    lsk: true,
                                    wav: true,
                                    neo: true
                                }
                            };
                            if (this.multiverse._chain.length > 1) {
                                this._logger.info('new block ' + newBlock.getHash() + ' references previous Block ' + newBlock.getPreviousHash() + ' for block ' + this.multiverse._chain[1].getHash());
                            }
                            this._logger.info('block ' + newBlock.getHeight() + ' considered next block in current multiverse ');
                            // RESTART MINING USED newBlock.getHash()
                            if (BC_BT_VALIDATION === true) {
                                delete options.childHeaders;
                                this.pubsub.publish('update.block.latest', options);
                            } else {
                                this.pubsub.publish('update.block.latest', options);
                            }
                            // notify the miner
                            this.node.broadcastNewBlock(newBlock, conn);
                        } else {
                            this._logger.info('block from peer ' + newBlock.getHeight() + ' is NOT next in multiverse block -> evaluating as sync candidate.');
                            return this.multiverse.addResyncRequest(newBlock, this.miningOfficer._canMine).then(shouldResync => {
                                if (shouldResync === true) {

                                    this._logger.info(newBlock.getHash() + ' <- new block: ' + newBlock.getHeight() + ' should sync request approved');

                                    // const host = conn.remoteHost || conn.remoteAddress
                                    // const port = conn.remotePort || conn.port

                                    /* eslint-disable */
                                    /////////// MULTIVERSE PROOF //////////////
                                    const obj = {
                                        data: {
                                            high: newBlock.getHeight(),
                                            low: new BN(newBlock.getHeight()).sub(new BN(7)).toNumber()
                                        },
                                        connection: conn
                                    };

                                    this.pubsub.publish('update.block.latest', {
                                        key: 'bc.block.latest',
                                        data: newBlock,
                                        force: true,
                                        mined: false
                                    });

                                    let storeChildHeaders = {
                                        btc: false,
                                        neo: true,
                                        lsk: false,
                                        eth: true,
                                        wav: true
                                    };
                                    if (BC_BT_VALIDATION === true) {
                                        storeChildHeaders = {
                                            btc: false,
                                            neo: false,
                                            lsk: false,
                                            eth: true,
                                            wav: false
                                        };
                                    }
                                    this.persistence.putChildHeaders(newBlock, storeChildHeaders).then(() => {
                                        // note the local machine does not broadcast this block update until the multiverse has been proven
                                        // parent headers do not form a chain
                                        this._emitter.emit('getmultiverse', obj);
                                    }).catch(err => {
                                        this._logger.error(err);
                                    });
                                } else {
                                    // this means the local peer has a better version of the chain and
                                    // therefore pushing it to the outside peer
                                    this._emitter.emit('sendblock', {
                                        data: newBlock,
                                        connection: conn
                                    });
                                }
                            });
                        }
                    }).catch(multiverseError => {
                        this._logger.error(multiverseError);
                    });
                } else {
                    this._logger.warn('block from peer invalid');
                }
            });
        }
    }

    getMultiverseHandler(conn, newBlocks) {
        // get the lowest of the current multiverse
        try {
            // REPLACE this.miningOfficer.stopMining(this._workerPool)
            this._logger.info('end mining');
            return true;
        } catch (e) {
            this._logger.error(e);
        }

        if (newBlocks === undefined || newBlocks.length < 7) {
            this._logger.warn('incomplete multiverse proof');
            return true;
        }

        const sorted = newBlocks.sort((a, b) => {
            if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
            }
            if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
            }
            return 0;
        });

        const newBlock = sorted[0];
        const highestBlock = this.multiverse.getHighestBlock();

        this._logger.info('comparable blocks: ' + sorted.length);
        this._logger.info(newBlock.getHash() + ' height: ' + newBlock.getHeight() + ' comparing with ' + highestBlock.getHash() + ' height: ' + highestBlock.getHeight());
        let conditional = false;
        // means the newBlock is the newest best highest block
        if (highestBlock.getHash() === newBlock.getHash()) {
            conditional = true;
        } else if (highestBlock !== undefined && sorted !== undefined && sorted.length > 0) {
            // conanaOut
            conditional = new BN(sorted[0].getTotalDistance()).gt(new BN(highestBlock.getTotalDistance()));
            if (conditional === false) {
                this._logger.info('purposed new block has lower total difficulty than current multiverse height');
            }
        } else if (sorted.length < 6) {
            conditional = true;
        }

        if (conditional === true) {
            // overwrite current multiverse
            const hasBlock = this.multiverse.hasBlock(sorted[0]);
            this._logger.info(newBlock.getHash() + ' approved --> assigning as current multiverse');
            this.multiverse._chain.length = 0;
            this.multiverse._chain = this.multiverse._chain.concat(sorted);
            this._logger.info('multiverse has been assigned');

            return this.syncSetBlocksInline(sorted).then(blocksStoredResults => {
                return this.persistence.put('bc.depth', sorted[0].getHeight()).then(() => {
                    // if the block is already in the multiverse dont conduct a full sync
                    if (hasBlock === false) {
                        this._logger.info('legacy multiverse did not include current block');

                        // determine if a sync is already in progress
                        return this.multiverse.isSyncLockActive().then(lock => {
                            if (lock === false) {
                                this._logger.info('lock is set to false');
                                return this.persistence.put('synclock', this.multiverse.getHighestBlock()).then(() => {
                                    this._logger.info('synclock was set to ' + this.multiverse.getHighestBlock());
                                    this.pubsub.publish('update.block.latest', {
                                        key: 'bc.block.latest',
                                        data: newBlock,
                                        force: true,
                                        multiverse: this.multiverse._chain,
                                        childHeaders: {
                                            btc: true,
                                            eth: true,
                                            neo: true,
                                            lsk: true,
                                            wav: true
                                        }
                                    });
                                    this.node.broadcastNewBlock(newBlock, conn);
                                    this._logger.debug('sync unlocked');
                                    const targetHeight = this.multiverse.getLowestBlock().getHeight() - 1;
                                    // dont have to sync
                                    if (targetHeight < 2) {
                                        return Promise.resolve(true);
                                    }

                                    this._emitter.emit('getblocklist', {
                                        data: {
                                            low: max(2, newBlock.getHeight() - 500),
                                            high: max(3, newBlock.getHeight())
                                        },
                                        connection: conn
                                    });

                                    return Promise.resolve(true);
                                }).catch(e => {
                                    this._logger.error(e);
                                    return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                                        this._logger.info('sync reset');
                                    }).catch(e => {
                                        this._logger.error(e);
                                    });
                                });
                            } else {
                                this.pubsub.publish('update.block.latest', {
                                    key: 'bc.block.latest',
                                    data: newBlock,
                                    force: true,
                                    multiverse: this.multiverse._chain
                                });
                                this.node.broadcastNewBlock(newBlock);
                                return Promise.resolve(true);
                            }
                        }).catch(e => {
                            this._logger.error(e);
                            return Promise.reject(e);
                        });
                    } else {
                        return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                            this._logger.info('sync reset');
                        });
                    }
                    // assign where the last sync began
                }).catch(e => {
                    this._logger.error(errToString(e));
                    return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                        this._logger.info('sync reset');
                    }).catch(e => {
                        this._logger.error(e);
                    });
                });
            }).catch(e => {
                this._logger.error(e);
                return Promise.resolve(true);
            });
        } else {
            this._logger.info('resync conditions failed');
            return this.persistence.put('synclock', getGenesisBlock()).then(() => {
                this._logger.info('sync reset');
            }).catch(e => {
                this._logger.error(e);
            });
        }
    }

    receiveSyncPeriod(peerIsSyncing) {
        this._logger.info('peer sync request');
    }

    /**
     * Start Server
     *
     * @param opts Options to start server with
     */
    startServer(opts) {
        this.server.run(opts);
    }

    requestExit() {
        ts.stop();
        this.miningOfficer.stop();
        return this._rovers.killRovers();
    }

    _writeRoverData(newBlock) {
        const dataPath = ensureDebugPath(`bc/rover-block-data.csv`);
        const rawData = JSON.stringify(newBlock);
        writeFileSync(dataPath, `${rawData}\r\n`, {
            encoding: 'utf8',
            flag: 'a'
        });
    }

    /**
     * Broadcast new block
     *
     * - peers
     * - pubsub
     * - ws
     *
     * This function is called by this._processMinedBlock()
     * @param newBlock
     * @param solution
     * @returns {Promise<boolean>}
     * @private
     */
    _broadcastMinedBlock(newBlock, solution) {
        if (newBlock === undefined) {
            return Promise.reject(new Error('cannot broadcast empty block'));
        }

        try {
            this._logger.info('broadcasting block challenge ' + newBlock.getHeight() + ' -> considered next block in current multiverse');
            this.node.broadcastNewBlock(newBlock);

            // NOTE: Do we really need nested try-catch ?
            try {
                const newBlockObj = _extends({}, newBlock.toObject(), {
                    iterations: solution.iterations,
                    timeDiff: solution.timeDiff
                });
                this.pubsub.publish('block.mined', {
                    type: 'block.mined',
                    data: newBlockObj
                });
            } catch (e) {
                return Promise.reject(e);
            }
        } catch (err) {
            return Promise.reject(err);
        }

        return Promise.resolve(true);
    }

    /**
     * Deals with unfinished block after the solution is found
     *
     * @param newBlock
     * @param solution
     * @returns {Promise<boolean>} Promise indicating if the block was successfully processed
     * @private
     */
    _processMinedBlock(newBlock, solution) {
        // TODO: reenable this._logger.info(`Mined new block: ${JSON.stringify(newBlockObj, null, 2)}`)
        // Trying to process null/undefined block
        if (newBlock === null || newBlock === undefined) {
            this._logger.warn('Failed to process work provided by miner');
            return Promise.resolve(false);
        }

        // Prevent submitting mined block twice
        if (this._knownBlocksCache.has(newBlock.getHash())) {
            this._logger.warn('received duplicate new block ' + newBlock.getHeight() + ' (' + newBlock.getHash() + ')');
            try {
                // REPLACE this.miningOfficer.stopMining(this._workerPool)
                this._logger.info('end mining');
                return Promise.resolve(true);
            } catch (e) {
                this._logger.warn('unable to stop miner');
                this._logger.error(e);
                return Promise.resolve(false);
            }
        }

        this._knownBlocksCache.set(newBlock.getHash(), 1);
        this._logger.info('submitting mined block to current multiverse');
        return this.multiverse.addNextBlock(newBlock).then(isNextBlock => {
            // $FlowFixMe
            // if (isNextBlock) {
            // TODO: this will break now that _blocks is not used in multiverse
            // if (this.multiverse.getHighestBlock() !== undefined &&
            //    this.multiverse.validateBlockSequenceInline([this.multiverse.getHighestBlock(), newBlock]) === true) {
            if (isNextBlock === true || BC_BT_VALIDATION === true) {
                let options = {
                    key: 'bc.block.latest',
                    data: newBlock,
                    mined: true
                };

                if (BC_BT_VALIDATION === true) {
                    options.force = true;
                }

                this.pubsub.publish('update.block.latest', options);
                this._server._wsBroadcastMultiverse(this.multiverse);
                this._logger.info('multiverse coverage: ' + this.multiverse._chain.length);
                // check if we know the peer
                return Promise.resolve(true);
            } else if (BC_BT_VALIDATION !== true) {
                this._logger.warn('local mined block ' + newBlock.getHeight() + ' does not stack on multiverse height ' + this.multiverse.getHighestBlock().getHeight());
                this._logger.warn('mined block ' + newBlock.getHeight() + ' cannot go on top of multiverse block ' + this.multiverse.getHighestBlock().getHash());
                return Promise.resolve(true);
                //return this.miningOfficer.rebaseMiner()
                //  .then((res) => {
                //    this._logger.info(res)
                //  })
                //  .catch((e) => {
                //    this._logger.error(errToString(e))
                //  })
            }
        }).catch(err => {
            this._logger.error(err);
            return Promise.resolve(false);
        });
    }
}

exports.Engine = Engine;
exports.default = Engine;
//# sourceMappingURL=index.js.map