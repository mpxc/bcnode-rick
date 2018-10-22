'use strict';

Object.defineProperty(exports, "__esModule", {
  value: true
});


const BN = require('bn.js'); /**
                              * Copyright (c) 2017-present, blockcollider.org developers, All rights reserved.
                              *
                              * This source code is licensed under the MIT license found in the
                              * LICENSE file in the root directory of this source tree.
                              *
                              * 
                              */

const BC_BT_VALIDATION = process.env.BC_BT_VALIDATION === 'true';
const { flatten } = require('ramda');

const { getGenesisBlock } = require('./genesis');
const { validateSequenceTotalDistance, validateSequenceDifficulty, isValidBlockCached, validateBlockSequence, getNewestHeader, childrenHeightSum } = require('./validation');
const { standardId } = require('./helper');
const { getLogger } = require('../logger');

class Multiverse {

  constructor(persistence) {
    this._persistence = persistence;
    this._id = standardId();
    this._chain = [];
    this._logger = getLogger(`bc.multiverse.${this._id}`, false);
    this._height = 0;
    this._created = Math.floor(Date.now() * 0.001);
  }

  get blocks() {
    return this._chain;
  }

  set blocks(blocks) {
    this._chain = blocks;
  }

  get blocksCount() {
    const blocks = this._chain;
    return blocks.length;
  }

  get persistence() {
    return this._persistence;
  }

  purge() {
    this._chain.length = 0;
    this._logger.info('metaverse has been purged');
  }

  /**
   * Get second to highest block in Multiverse
   */
  async getParentHighestBlock() {
    try {
      const par = await this.persistence.get('bc.block.parent', { asBuffer: true, softFail: true });
      return Promise.resolve(par);
    } catch (err) {
      this._logger.debug(err);
      return Promise.resolve(false);
    }
  }

  /**
   * Accessor for validation function
   * @returns {*}
   */
  validateBlockSequence(blocks) {
    return validateBlockSequence(blocks);
  }

  /**
   * Valid Block Range
   * @returns {*}
   */
  async validateBlockSequenceInline(blocks) {
    if (blocks === undefined || blocks.length < 1) {
      return Promise.resolve(false);
    }
    const sorted = blocks.sort((a, b) => {
      if (a.getHeight() < b.getHeight()) {
        return 1;
      }
      if (a.getHeight() > b.getHeight()) {
        return -1;
      }
      return 0;
    });
    // check if the actually sequence itself is valid
    const upperBound = sorted[0];
    const lowerBound = sorted[sorted.length - 1];

    try {
      const upperBoundChild = await this.persistence.get(`pending.bc.block.${sorted[0].getHeight()}`);
      // current pending block does not match the purposed block at that height
      if (upperBoundChild === undefined || upperBound.getHash() !== upperBoundChild.getPreviousHash()) return Promise.reject(new Error('pending block does not match purposed block'));
      // add the child block of the sequence
      sorted.unshift(upperBoundChild);
    } catch (err) {
      this._logger.warn('load warning');
    }
    if (lowerBound === 1) {
      // if at final depth this will equal 1 or the genesis block
      const lowerBoundParent = await this.persistence.get('bc.block.1');
      if (lowerBound.getPreviousHash() !== lowerBoundParent.getHash()) return Promise.reject(new Error('sync did not resolve to genesis block'));
      // add the genesis block to the sequence
      sorted.push(lowerBoundParent);
    }
    // finally check the entire sequence
    // enabled during AT
    // if (!validateBlockSequence(sorted)) return Promise.reject(new Error('block sequence invalid'))

    return Promise.resolve(true);
  }

  /**
   * Get highest block in Multiverse
   * @returns {*}
   */
  getHighestBlock() {
    if (this._chain.length === 0) {
      return;
    }
    return this._chain[0];
  }

  /**
   * Get lowest block by block key
   * @returns {*}
   */
  getLowestBlock() {
    if (this._chain.length > 0) {
      return this._chain[this._chain.length - 1];
    }
    return null;
  }

  /**
   * check if a block exists
   * @param newBlock
   * @returns {boolean}
   */
  hasBlock(newBlock) {
    if (this._chain.length < 1) {
      return false;
    }
    return this._chain.reduce((state, b) => {
      if (state === true) {
        return state;
      } else if (b.getHash() === newBlock.getHash()) {
        return true;
      }
      return false;
    }, false);
  }

  /**
   * Check if immmediate height is better
   * @param newBlock
   * @returns {boolean}
   */
  async addBestBlock(newBlock) {
    const currentHighestBlock = this.getHighestBlock();
    const currentParentHighestBlock = await this.getParentHighestBlock();
    if (currentHighestBlock === null || currentHighestBlock === undefined) {
      // assume we always have current highest block
      this._logger.error('Cannot get currentHighestBlock');
      this._logger.info('bestBlock: failed  ');
      return Promise.resolve(true);
    }
    // if no block is available go by total difficulty
    // FAIL if new block not within 16 seconds of local time
    // if (newBlock.getTimestamp() + 16 < Math.floor(Date.now() * 0.001)) {
    //  this._logger.info('bestBlock: failed timestamp ')
    //  return false
    // }
    // if there is no current parent, this block is the right lbock
    if (currentParentHighestBlock !== false && newBlock.getPreviousHash() === currentParentHighestBlock.getHash()) {
      if (new BN(newBlock.getTotalDistance()).gt(new BN(currentHighestBlock.getTotalDistance()))) {
        this._logger.info('best block failed newBlock total distance < current block total distance');
        this._chain.length = 0;
        this._chain.push(newBlock);
        return Promise.resolve(true);
      }
    }

    if (currentParentHighestBlock === false) {
      if (new BN(newBlock.getTotalDistance()).gt(new BN(currentHighestBlock.getTotalDistance()))) {
        this._logger.info('best block failed newBlock total distance < current block total distance');
        this._chain.length = 0;
        this._chain.push(newBlock);
        return Promise.resolve(true);
      }
      return Promise.resolve(false);
    }

    // FAIL if newBlock total difficulty <  currentHighestBlock
    if (new BN(newBlock.getTotalDistance()).lt(new BN(currentHighestBlock.getTotalDistance()))) {
      this._logger.info('best block failed newBlock total distance < current block total distance');
      return Promise.resolve(false);
    }
    // if the current block at the same height is better switch
    if (currentParentHighestBlock !== null && currentParentHighestBlock !== undefined && newBlock.getPreviousHash() === currentParentHighestBlock.getHash()) {
      // validateBlockSequence([newBlock, currentParentHighestBlock]) === true) {
      this._logger.info('new block at its height greater total than block in multiverse');
      this._chain.shift();
      this._chain.unshift(newBlock);
      return Promise.resolve(true);
    }
    return Promise.resolve(false);
  }

  /**
   * Eval and update multiverse with next block
   * @param block New block
   * @returns {boolean}
   */
  async addNextBlock(newBlock, type = 0) {
    // return false for empty block
    if (newBlock === undefined || newBlock === null) {
      this._logger.warn('no block was given to evaluate');
      return Promise.resolve(false);
    }

    if (newBlock.getHeight() === '1' || newBlock.getHeight() === 1) {
      this._logger.warn('cant recieve genesis block from peer');
      return Promise.resolve(false);
    }

    const newBlockHeaders = newBlock.getBlockchainHeaders();
    if (newBlock.getHeight() !== 1 && newBlockHeaders.getBtcList().length > 0 && BC_BT_VALIDATION === true && new BN(newBlockHeaders.getBtcList()[0].getHeight()).gt(new BN(541000)) === true) {
      return Promise.resolve(false);
    } else if (newBlock.getHeight() !== 1 && newBlockHeaders.getBtcList().length > 0 && new BN(newBlockHeaders.getBtcList()[0].getHeight()).gt(new BN(545000)) === true && new BN(newBlock.getHeight()).lt(new BN(530000)) === true) {
      return Promise.resolve(false);
    }
    // if there are no blocks in the multiverse this block is the highest
    // in default setup the contructor loads the genesis block into the multiverse
    if (this._chain.length === 0) {
      this._chain.push(newBlock);
      return Promise.resolve(true);
    }

    const currentHighestBlock = await this.persistence.get('bc.block.latest');
    // PASS
    // no other candidate in Multiverse
    if (currentHighestBlock === null || currentHighestBlock === undefined) {
      this._chain.unshift(newBlock);
      return Promise.resolve(true);
    }

    // HOTSWAP - NO SYNC
    // this is a hotswap in at the current block height for a new block
    // TODO: Consider moving this to resync (except we dont want sync triggered)
    const currentHighestParent = await this.persistence.get('bc.block.parent', { asBuffer: true, softFail: true });
    if (currentHighestParent !== false && new BN(currentHighestBlock.getTotalDistance()).lt(new BN(newBlock.getTotalDistance())) === true && newBlock.getPreviousHash() === currentHighestParent.getHash() && validateSequenceDifficulty(currentHighestParent, newBlock) === true) {
      if (new BN(newBlock.getTotalDistance()).gt(new BN(currentHighestBlock.getTotalDistance())) === true) {
        this._chain.shift();
        this._chain.unshift(newBlock);
        this._logger.warn('hs occured ' + newBlock.getHeight() + ' <-> ' + newBlock.getHeight() + ' all clear <- ref hash' + newBlock.getHash().slice(0, 12));
        return Promise.resolve(true);
      }
    }

    const roveredBlockHeaders = await this.validateRoveredBlocks(newBlock);
    if (roveredBlockHeaders === false) {
      this._logger.info('assert rover block sequence <- invalid');
      return Promise.resolve(false);
    }

    if (newBlock.getHeight() === 1 || newBlock.getHeight() === '1') {
      // block being sent is genesis block
      return Promise.resolve(false);
    }

    this._logger.info('newBlock height: ' + newBlock.getHeight());
    this._logger.info('currentHighestBlock height: ' + currentHighestBlock.getHeight());
    if (newBlock.getHeight() - 1 !== currentHighestBlock.getHeight()) {
      // block being sent is genesis block
      this._logger.warn('block does not increment the multichain sequence');
      return this.addBestBlock(newBlock);
    }

    this._logger.warn('child height new block #' + newBlock.getHeight() + ': ' + childrenHeightSum(newBlock));
    this._logger.warn('child height previous block #' + currentHighestBlock.getHeight() + ': ' + childrenHeightSum(currentHighestBlock));
    if (childrenHeightSum(newBlock) + 3 < childrenHeightSum(currentHighestBlock)) {
      this._logger.warn('connection child chain weight is below threshold');
      // after block height 500000 resume traditional assertions even if BC_BT_VALIDATION is true
      return Promise.resolve(false);
    }

    // if difficulty is invalid and we have not enabled BC_BT_VALIDATION on this node reject as next block
    if (!validateSequenceDifficulty(currentHighestBlock, newBlock)) {
      this._logger.info('invalid difficulties');
      return Promise.resolve(false);
    }
    // if it has an invalid total distance and we have not enabled BC_BT_VALIDATION fail the block
    if (!validateSequenceTotalDistance(currentHighestBlock, newBlock)) {
      this._logger.info('invalid total distance calculation');
      return Promise.resolve(false);
    }

    if (childrenHeightSum(newBlock) === childrenHeightSum(currentHighestBlock)) {
      this._logger.warn('evaluating child chain weight of equality conditional');
      const newBlockNewestChildHeader = getNewestHeader(newBlock);
      const currentBlockNewestChildHeader = getNewestHeader(currentHighestBlock);

      this._logger.info('new block newest child header: ' + newBlockNewestChildHeader);
      this._logger.info('current block newest child header: ' + currentBlockNewestChildHeader);
      if (new BN(getNewestHeader(newBlock).timestamp).lt(new BN(getNewestHeader(currentHighestBlock).timestamp)) === true) {
        return Promise.resolve(false);
      }
    }

    // FAIL
    // case fails over into the resync
    if (newBlock.getHeight() - 7 > currentHighestBlock.getHeight()) {
      return Promise.resolve(false);
    }

    this._logger.debug(' highestBlock hash - ' + currentHighestBlock.getHash());
    this._logger.debug(' highestBlock previousHash - ' + currentHighestBlock.getPreviousHash());
    this._logger.debug(' highestBlock height - ' + currentHighestBlock.getHeight());
    this._logger.debug(' highestBlock difficulty - ' + currentHighestBlock.getDifficulty());
    this._logger.debug(' newBlock hash - ' + newBlock.getHash());
    this._logger.debug(' newBlock difficulty - ' + newBlock.getDifficulty());
    this._logger.debug(' newBlock previousHash - ' + newBlock.getPreviousHash());
    // Fail is the block hashes are identical
    if (currentHighestBlock !== undefined && newBlock.getHash() === currentHighestBlock.getHash()) {
      this._logger.warn('newBlock hash === currentHighestBlock hash');
      return Promise.resolve(false);
    }

    // FAIL
    // case fails over into the resync
    if (newBlock.getHeight() < currentHighestBlock.getHeight()) {
      return Promise.resolve(false);
    }

    // if (new BN(newBlock.getTotalDistance()).lt(new BN(currentHighestBlock.getTotalDistance()))) {
    //  this._logger.warn('new Block totalDistance ' + newBlock.getTotalDistance() + 'less than currentHighestBlock' + currentHighestBlock.getTotalDistance())
    //  return Promise.resolve(false)
    // }

    // FAIL
    // if newBlock does not include additional rover blocks
    if (newBlock.getBlockchainHeadersCount() === '0') {
      this._logger.warn('new Block total headers count is below threshold');
      return Promise.resolve(false);
    }

    // AT STRICT TIMELINE
    // without ire from retrograde

    // if malformed timestamp referenced from previous block with three second lag
    if (newBlock.getTimestamp() + 3 <= currentHighestBlock.getTimestamp()) {
      this._logger.info('purposed block ' + newBlock.getHash() + ' has invalid timestamp ' + newBlock.getTimestamp() + ' from current height timestamp ' + currentHighestBlock.getTimestamp());
      return Promise.resolve(false);
    }
    // FAIL if timestamp of block is greater than 47 seconds from system time
    if (newBlock.getTimestamp() + 47 < Math.floor(Date.now() * 0.001)) {
      this._logger.info('purposed block ' + newBlock.getHash() + ' has invalid timestamp ' + newBlock.getTimestamp() + ' from current height timestamp ' + currentHighestBlock.getTimestamp());
      return Promise.resolve(false);
    }

    // FAIL
    // if newBlock does not reference the current highest block as it's previous hash
    if (newBlock.getPreviousHash() !== currentHighestBlock.getHash()) {
      this._logger.info('purposed block ' + newBlock.getHash() + ' previous hash not current highest ' + currentHighestBlock.getHash());
      return this.addBestBlock(newBlock);
    }
    // FAIL
    // if newBlock does not reference the current highest block as it's previous hash
    // note this ignores the first block immediately following the genesis block due to lack of rovered blocks in the genesis block
    if (newBlock.getHeight() > 2 && validateBlockSequence([newBlock, currentHighestBlock]) !== true) {
      this._logger.info('addition of block ' + newBlock.getHash() + ' creates malformed child blockchain sequence');
      return this.addBestBlock(newBlock);
    }
    // PASS
    // add the new block to the parent position
    this._chain.unshift(newBlock);

    // const validRovers = validateRoveredSequences([newBlock, currentHighestBlock])
    // if (validRovers === false) {
    //  this._logger.info('multiverse contains wayward rovers')
    //  // disabled until AT
    //  // return this.addBestBlock(newBlock)
    // }

    if (this._chain.length > 7) {
      this._chain.pop();
    }

    return Promise.resolve(true);
  }

  async isSyncLockActive() {
    try {
      const synclock = await this.persistence.get('synclock');

      if (synclock.getHeight() !== 1 && synclock.getTimestamp() + 5 < Math.floor(Date.now() * 0.001)) {
        await this.persistence.put('synclock', getGenesisBlock());
        this._logger.warn('sync lock is stale resetting');
        return Promise.resolve(false);
      } else if (synclock.getHeight() === 1) {
        return Promise.resolve(false);
      }
      return Promise.resolve(true);
    } catch (err) {
      this._logger.error(err);
      return Promise.resolve(true);
    }
  }

  /**
   * Check if block sould be queued for resync as a potentially bettter path
   * if returns true miner is paused
   * @param newBlock
   * @returns {boolean}
   */
  async addResyncRequest(newBlock, strict = true) {
    // check if the node is currently syncing, if so do not approve a sync
    const syncLockActive = await this.isSyncLockActive();

    if (newBlock.getHeight() === '1' || newBlock.getHeight() === 1) {
      this._logger.warn('cant recieve genesis block from peer');
      return Promise.resolve(false);
    }

    if (syncLockActive === true) {
      this._logger.info('proposed block ' + newBlock.getHeight() + ' not accepted <- active sync lock');
      return Promise.resolve(false);
    }

    const currentHighestBlock = await this.persistence.get('bc.block.latest');
    const currentParentHighestBlock = await this.getParentHighestBlock();
    const newBlockHeaders = newBlock.getBlockchainHeaders();

    if (newBlock.getHeight() !== 1 && newBlockHeaders.getBtcList().length > 0 && BC_BT_VALIDATION === true && new BN(newBlockHeaders.getBtcList()[0].getHeight()).gt(new BN(541000)) === true) {
      this._logger.info('failed resync <- BC_BT_VALIDATION');
      return Promise.resolve(false);
    } else if (newBlock.getHeight() !== 1 && newBlockHeaders.getBtcList().length > 0 && new BN(newBlockHeaders.getBtcList()[0].getHeight()).gt(new BN(545000)) === true && new BN(newBlock.getHeight()).lt(new BN(530000)) === true) {
      return Promise.resolve(false);
    }

    try {
      const roveredBlockHeaders = await this.validateRoveredBlocks(newBlock);
      if (roveredBlockHeaders === false) {
        this._logger.warn('rover coverage of child headers is low');
        return Promise.resolve(false);
      }
    } catch (err) {
      this._logger.error(err);
    }

    if (this._chain.length === 0) {
      this._logger.info('passed sync req <- currentHighestBlock not set');
      return Promise.resolve(true);
    }

    // pass if no highest block exists go with current
    if (currentHighestBlock === null) {
      this._logger.info('passed resync req <- currentHighestBlock not set');
      return Promise.resolve(true);
    }

    // only block is the genesis block
    if (currentHighestBlock.getHeight() === 1 && newBlock.getHeight() > 1) {
      this._logger.info('passed resync req <- new block above genesis');
      return Promise.resolve(true);
    }

    // Fail if the block hashes are identical
    if (newBlock.getHash() === currentHighestBlock.getHash()) {
      this._logger.info('failed resync req <- newBlock non-unique hash');
      return Promise.resolve(false);
    }

    // current chain is malformed and new block is not
    const validNewBlock = await isValidBlockCached(this.persistence, newBlock);
    const validCurrentBlock = await isValidBlockCached(this.persistence, currentHighestBlock);
    if (validNewBlock === true && validCurrentBlock === false) {
      this._logger.info('passed sync req <- currentHighestBlock malformed');
      return Promise.resolve(true);
    }

    this._logger.warn('child height new block: ' + childrenHeightSum(newBlock));
    this._logger.warn('child height previous block: ' + childrenHeightSum(currentHighestBlock));
    if (childrenHeightSum(newBlock) + 3 < childrenHeightSum(currentHighestBlock)) {
      this._logger.warn('connection chain weight is below threshold');
      return Promise.resolve(false);
    }

    // PASS if current highest block is older than 58 seconds from local time
    if (new BN(new BN(currentHighestBlock.getTimestamp()).add(new BN(58))).lt(new BN(Math.floor(Date.now() * 0.001))) === true && new BN(currentHighestBlock.getTotalDistance()).lt(new BN(newBlock.getTotalDistance())) === true && new BN(currentHighestBlock.getHeight()).lte(new BN(newBlock.getHeight())) === true && new BN(getNewestHeader(newBlock).timestamp).gt(new BN(getNewestHeader(currentHighestBlock).timestamp)) === true) {
      this._logger.info('current chain is stale chain new child time: ' + getNewestHeader(newBlock).timestamp + ' current child time: ' + getNewestHeader(currentHighestBlock).timestamp);
      return Promise.resolve(true);
    }

    // FAIL if new block not within 31 seconds of local time
    if (new BN(newBlock.getHeight()).gt(100000) === true && newBlock.getTimestamp() + 61 < Math.floor(Date.now() * 0.001)) {
      this._logger.warn('failed resync req: purposed block time has expired');
      return Promise.resolve(false);
    }

    // FAIL if new block not within 31 seconds of local time
    if (new BN(newBlock.getHeight()).gt(100000) === true && newBlock.getTimestamp() - 61 > Math.floor(Date.now() * 0.001)) {
      this._logger.warn('failed resync req: purposed block beyond temporal limit');
      return Promise.resolve(false);
    }

    if (this._chain.length < 2) {
      this._logger.info('determining if chain current total distance is less than new block');
      if (new BN(currentHighestBlock.getTotalDistance()).lt(new BN(newBlock.getTotalDistance())) === true && new BN(childrenHeightSum(currentHighestBlock)).lt(new BN(childrenHeightSum(newBlock))) === true) {
        const passed = await this.validateRoveredBlocks(newBlock);
        if (passed === true) {
          return Promise.resolve(true);
        }
      }
    }

    if (new BN(currentHighestBlock.getTotalDistance()).lt(new BN(newBlock.getTotalDistance())) === true &&
        (new BN(currentHighestBlock.getHeight()).add(new BN(10)).lte(new BN(newBlock.getHeight())) === true)) {
      const passed = await this.validateRoveredBlocks(newBlock)
      if (passed === true) {
        this._logger.info('skip ahead to block: ' + currentHighestBlock.getHeight())
        return Promise.resolve(true)
      }
    }

    if (currentParentHighestBlock === null && currentHighestBlock !== null) {
      if (new BN(newBlock.getTotalDistance()).gt(new BN(currentHighestBlock.getTotalDistance())) && new BN(newBlock.getDifficulty()).gt(new BN(currentHighestBlock.getDifficulty())) === true) {
        const passed = this.validateRoveredBlocks(newBlock);
        if (passed === true) {
          return Promise.resolve(true);
        }
      }
    }

    // FAIL if newBlock total difficulty <  currentHighestBlock
    if (new BN(currentHighestBlock.getTotalDistance()).gt(new BN(newBlock.getTotalDistance())) === true) {
      this._logger.info('cancel resync req <- new block distance ' + newBlock.getTotalDistance() + ' is lower than highest block ' + currentHighestBlock.getTotalDistance());
      return Promise.resolve(false);
    }

    // pick the chain we have rovered blocks for
    if (childrenHeightSum(newBlock) <= childrenHeightSum(currentHighestBlock)) {
      this._logger.warn('child height new block: ' + childrenHeightSum(newBlock));
      this._logger.warn('child height previous block: ' + childrenHeightSum(currentHighestBlock));

      const passedNewBlock = await this.validateRoveredBlocks(newBlock);
      if (passedNewBlock === true) {
        const passedOldBlock = await this.validateRoveredBlocks(currentHighestBlock);
        if (passedOldBlock === false) {
          return Promise.resolve(true);
        }
      }
      return Promise.resolve(false);
    }
    return Promise.resolve(false);
  }

  async validateRoveredBlocks(block) {
    // construct key array like ['btc.block.528089', ..., 'wav.block.1057771', 'wav.blocks.1057771']
    this._logger.info('evaluate rovered headers weight');
    try {
      const receivedHeaders = block.getBlockchainHeaders();
      const receivedBlocks = flatten(Object.values(block.getBlockchainHeaders().toObject()));

      let btcHeight = block.getBlockchainHeaders().getBtcList()[0].getHeight()
      if (btcHeight > 553300) {
        this._logger.warn('rejecting shitty btc block with height=' + btcHeight)
        return false
      }
      let ethHeight = block.getBlockchainHeaders().getEthList()[0].getHeight()
      if (ethHeight > 6789430) {
        this._logger.warn('rejecting shitty eth block with height=' + ethHeight)
        return false
      }

      const keys = receivedBlocks
      // $FlowFixMe - Object.values is not generic
      .map(({ blockchain, height }) => `${blockchain}.block.${height}`);

      const blocks = await this.persistence.getBulk(keys);

      let valid = keys.length === blocks.length;

      if (!valid) {
        /* eslint-disable */
        const previousKeys = receivedBlocks
        // $FlowFixMe - Object.values is not generic
        .map(b => `${b.blockchain}.block.${b.height - 1}`);
        //console.log('------- KEYS ---------')
        //console.log(keys)
        //console.log('------- PREV KEYS ---------')
        //console.log(previousKeys)
        const parentBlock = await this.persistence.get('bc.block.parent');
        // if the parent block is one accept the given child headers
        if (parentBlock.getHeight() === '1' || parentBlock.getHeight() === 1) {
          return Promise.resolve(true);
        }

        const previousBlocks = await this.persistence.getBulk(previousKeys);

        //if(previousBlocks === undefined || previousBlocks === false || previousBlocks.length !== keys.length){
        //  this._logger.warn('previous blocks not available for sequence confirmation')
        //  return Promise.resolve(false)
        //}

        const latestBlockchainNames = blocks.map(b => {
          return b.getBlockchain();
        });

        const previousBlockchainNames = previousBlocks.map(b => {
          return b.getBlockchain();
        });

        const missingBlockchainNames = keys.reduce((missing, key) => {
          if (latestBlockchainNames.indexOf(key) < 0) {
            missing.push(key);
          }
          return missing;
        }, []);

        const missingBlocks = missingBlockchainNames.reduce((missing, blockchain) => {
          let list = [];
          let lowest;
          if (blockchain === 'btc') {
            list = receivedHeaders.getBtcList().sort((a, b) => {
              if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
              }
              if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
              }
              return 0;
            });
            if (list.length > 0) {
              lowest = list.pop();
            }
          } else if (blockchain === 'eth') {
            list = receivedHeaders.getEthList().sort((a, b) => {
              if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
              }
              if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
              }
              return 0;
            });
            if (list.length > 0) {
              lowest = list.pop();
            }
          } else if (blockchain === 'wav') {
            list = receivedHeaders.getWavList().sort((a, b) => {
              if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
              }
              if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
              }
              return 0;
            });
            if (list.length > 0) {
              lowest = list.pop();
            }
          } else if (blockchain === 'neo') {
            list = receivedHeaders.getNeoList().sort((a, b) => {
              if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
              }
              if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
              }
              return 0;
            });
            if (list.length > 0) {
              lowest = list.pop();
            }
          } else if (blockchain === 'lsk') {
            list = receivedHeaders.getLskList().sort((a, b) => {
              if (new BN(a.getHeight()).gt(new BN(b.getHeight())) === true) {
                return -1;
              }
              if (new BN(a.getHeight()).lt(new BN(b.getHeight())) === true) {
                return 1;
              }
              return 0;
            });
            if (list.length > 0) {
              lowest = list.pop();
            }
          }
          if (lowest !== undefined) {
            missing.push(lowest);
          }
          return missing;
        }, []);

        //console.log('------- BLOCKS ON DISK ---------')
        //console.log(latestBlockchainNames)
        //console.log('------- PREVIOUS BLOCKS ON DISK ---------')
        //console.log(previousBlockchainNames)
        //console.log('------- UNROVERED BLOCKS ---------')
        //console.log(missingBlockchainNames)

        let falseBlock = false;
        const correctSequence = missingBlocks.reduce((valid, block) => {
          if (block.getBlockchain() === 'btc' && BC_BT_VALIDATION === true) {
            if (new BN(block.getHeight()).gt(new BN(541000)) === true) {
              valid = false;
              falseBlock = true;
            }
          }
          if (valid === false) {
            const count = previousBlocks.reduce((updateValid, pb) => {
              if (block.getBlockchain() === pb.getBlockchain()) {
                //console.log('eval blockchain ' + pb.getBlockchain() + ' previousHash: ' + pb.getPreviousHash() + ' hash: ' + block.getHash())
                if (validateBlockSequence([pb, block])) {
                  //console.log('for blockchain ' + pb.getBlockchain() + ' sequence is INVALID previousHash: ' + pb.getPreviousHash() + ' hash: ' + block.getHash())
                  updateValid++;
                } else if (pb.getHeight() + 1 === block.getHeight()) {
                  // permitted only in BT
                  updateValid++;
                } else {
                  updateValid--;
                }
              }
              return updateValid;
            }, 0);
            if (count >= 0) {
              valid = true;
            }
          }
          return valid;
        }, false);

        this._logger.warn('purposed child blocks not known by rover <- correctSequence: ' + correctSequence);
        if (falseBlock === true) {
          return Promise.resolve(false);
        }
        return Promise.resolve(correctSequence);
      }
    } catch (err) {
      this._logger.error(err);
    }

    // const pairs = zip(receivedBlocks, blocks)

    // const isChained = Promise.resolve(all(flag => flag === true, pairs.map(([received, expected]) => {
    //  // $FlowFixMe
    //  return received.hash === expected.getHash() &&
    //    // $FlowFixMe
    //    received.height === expected.getHeight() &&
    //    // $FlowFixMe
    //    received.merkleRoot === expected.getMerkleRoot() &&
    //    // $FlowFixMe
    //    received.timestamp === expected.getTimestamp()
    // })))

    return Promise.resolve(true);
    // disabled until AT
    // if (isChained !== true) {
    //  this._logger.info('failed chained check')
    // }
    // return isChained
  }

  /**
   * Get multiverse as nested `BcBlock` array
   * @returns {*}
   */
  toArray() {
    return this._chain;
  }

  /**
   * Get multiverse as flat `BcBlock` array
   */
  toFlatArray() {
    const blocks = this.toArray();
    return flatten(blocks);
  }

  // NOTE: Multiverse print disabled. Why?
  print() {
    // this._logger.info(this._blocks)
    this._logger.info('multiverse print disabled');
  }
}

exports.Multiverse = Multiverse;
exports.default = Multiverse;
//# sourceMappingURL=multiverse.js.map
