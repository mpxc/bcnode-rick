'use strict';

Object.defineProperty(exports, "__esModule", {
  value: true
});
exports.isValidBlock = isValidBlock;
exports.isValidChildAge = isValidChildAge;
exports.isValidBlockCached = isValidBlockCached;
exports.getNewestHeader = getNewestHeader;
exports.blockchainHeadersAreChain = blockchainHeadersAreChain;
exports.validateRoveredSequences = validateRoveredSequences;
exports.validateSequenceTotalDistance = validateSequenceTotalDistance;
exports.validateSequenceDifficulty = validateSequenceDifficulty;
exports.validateBlockSequence = validateBlockSequence;
exports.childrenHighestBlock = childrenHighestBlock;
exports.childrenHeightSum = childrenHeightSum;
/**
 * Copyright (c) 2017-present, Block Collider developers, All rights reserved.
 *
 * This source code is licensed under the MIT license found in the
 * LICENSE file in the root directory of this source tree.
 *
 * 
 */
/* eslint-disable */
const { inspect } = require('util');
const BN = require('bn.js');
const {
  all,
  aperture,
  equals,
  flatten,
  fromPairs,
  head,
  identity,
  last,
  reject,
  sort,
  sum
} = require('ramda');

const { getLogger } = require('../logger');
const { blake2bl } = require('../utils/crypto');
const { concatAll } = require('../utils/ramda');
const { BcBlock, BlockchainHeader, Block } = require('../protos/core_pb');
const {
  getExpFactorDiff,
  getNewBlockCount,
  getDiff,
  getChildrenBlocksHashes,
  getChildrenRootHash,
  blockchainMapToList,
  createMerkleRoot,
  prepareWork,
  distance
} = require('../mining/primitives');
const GENESIS_DATA = require('./genesis.raw');
const FINGERPRINTS_TEMPLATE = require('../utils/templates/blockchain_fingerprints.json');
const MINIMAL_DIFFICULTY = new BN(290112262029012);

const DF_CONFIG = exports.DF_CONFIG = fromPairs(FINGERPRINTS_TEMPLATE.blockchainHeaders.map(({ name, dfNumerator, dfDenominator, dfVoid, dfBound }) => [name, { dfNumerator, dfDenominator, dfVoid, dfBound }]));

const logger = getLogger(__filename);

function isValidBlock(newBlock, type = 0) {
  if (newBlock === undefined) {
    this._logger.warn('candidate block is undefined');
    return false;
  }
  if (newBlock.getBlockchainHeaders === undefined) {
    logger.warn('candidate block has incomplete child headers references');
    //return false
  }
  let btcHeight = newBlock.getBlockchainHeaders().getBtcList()[0].getHeight();
  let btcCountHeight = Math.floor(Math.abs(Date.now() - Date.parse("31 Oct 2018 15:43:21 GMT+1")) / 36e5);
  let btcApproxHeight = 548140 + (btcCountHeight * 7) + (7 * 2);
  if (btcHeight > btcApproxHeight) {
    logger.warn('rejecting shitty btc block with height=' + btcHeight + ' expected(max)=' + btcApproxHeight);
    return false;
  }
  let ethHeight = newBlock.getBlockchainHeaders().getEthList()[0].getHeight();
  let ethCountHeight = Math.floor(Math.abs(Date.now() - Date.parse("31 Oct 2018 15:45:56 GMT+1")) / 36e5);
  let ethApproxHeight = 6618108 + (ethCountHeight * 252) + (252 * 2);
  if (ethHeight > ethApproxHeight) {
    logger.warn('rejecting shitty eth block with height=' + ethHeight + ' expected(max)=' + ethApproxHeight);
    return false;
  }
  // blocks may pass before the soft opening limit of 151500 blocks
  if (new BN(newBlock.getHeight()).lt(new BN(151500)) === true) {
    return true;
  }
  logger.info('determining block validity');
  // if (!theBlockChainFingerPrintMatchGenesisBlock(newBlock)) {
  //  logger.warn('failed: theBlockChainFingerPrintMatchGenesisBlock')
  //  return false
  // } // DISABLED UNTIL AT
  if (!numberOfBlockchainsNeededMatchesChildBlock(newBlock)) {
    logger.warn('failed: numberOfBlockchainsNeededMatchesChildBlock');
    return false;
  }
  if (!ifMoreThanOneHeaderPerBlockchainAreTheyOrdered(newBlock)) {
    logger.warn('failed: ifMoreThanOneHeaderPerBlockchainAreTheyOrdered');
    return false;
  }
  if (!isChainRootCorrectlyCalculated(newBlock)) {
    logger.warn('failed: isChainRootCorrectlyCalculated');
    return false;
  }
  if (!isFieldLengthBounded(newBlock)) {
    logger.warn('failed: isFieldLengthBounded');
    return false;
  }
  if (!isMerkleRootCorrectlyCalculated(newBlock)) {
    logger.warn('failed: isMerkleRootCorrectlyCalculated');
    return false;
  }
  if (!isValidChildAge(newBlock)) {
    return false;
  }
  if (!isDistanceAboveDifficulty(newBlock)) {
    logger.warn('failed: isDistanceAboveDifficulty');
    return false;
  }
  if (!isDistanceCorrectlyCalculated(newBlock)) {
    logger.warn('failed: isDistanceCorrectlyCalculated');
    return false;
  }
  if (type === 0) {
    //if (!areDarkFibersValid(newBlock)) {
    //  logger.warn('failed: areDarkFibersValid')
    //  return false
    //}
  }
  return true;
}

function isValidChildAge(newBlock, type = 0) {
  const newestHeader = getNewestHeader(newBlock);

  logger.info('confirming valid child ages for new block');
  if (newestHeader === false) {
    logger.warn('failed: validChildAge no upper limit child header found');
    return false;
  }

  // add the offset for dark fiber
  const bcBlockTimestamp = new BN(newBlock.getTimestamp()).mul(new BN(1000)).toNumber();
  const highRangeLimit = 59 * 1000;
  const lowRangeLimit = 29 * 1000;
  const newestHeaderDFBound = DF_CONFIG[newestHeader.blockchain].dfBound * 1000;
  const newestHeaderTimestamp = new BN(newestHeader.timestamp).add(new BN(newestHeaderDFBound)).toNumber();
  const upperTimestampLimit = new BN(newestHeaderTimestamp).add(new BN(highRangeLimit)).toNumber();
  const lowerTimestampLimit = new BN(newestHeaderTimestamp).sub(new BN(lowRangeLimit)).toNumber();

  logger.info('bcblocktimestamp timestamp: ' + bcBlockTimestamp);
  logger.info('newest header bound: ' + newestHeaderDFBound);
  logger.info('newest header timestamp: ' + newestHeader.timestamp);
  logger.info('upperTimestampLimit: ' + upperTimestampLimit);
  logger.info('lowerTimestampLimit: ' + lowerTimestampLimit);

  /* eslint-enable */
  if (new BN(bcBlockTimestamp).gt(new BN(upperTimestampLimit)) === true) {
    logger.warn('failed: isValidChildAge upper limit');
    return false;
  }

  if (new BN(bcBlockTimestamp).lt(new BN(lowerTimestampLimit)) === true) {
    logger.warn('failed: isValidChildAge lower limit');
    return false;
  }
  return true;
}

async function isValidBlockCached(persistence, newBlock, type = 0) {
  try {
    if (new BN(newBlock.getHeight()).lt(new BN(151500)) === true) {
      return Promise.resolve(true);
    }
    const cached = await persistence.get('valid_' + newBlock.getHash());
    // if of type: string 'false' it means the block is invalid
    return Promise.resolve(cached === 'true');
  } catch (_) {
    try {
      const valid = isValidBlock(newBlock, type);
      await persistence.put('valid_' + newBlock.getHash(), String(valid));
      // return this block in wrhatever state it was validated
      return Promise.resolve(valid);
    } catch (err) {
      // error attempting to parse this as a block, reject
      logger.error(err);
      return Promise.resolve(false);
    }
  }
}

function getNewestHeader(newBlock) {
  logger.info('getting block height ' + newBlock.getHeight());
  if (newBlock === undefined || newBlock.getBlockchainHeaders === undefined) {
    logger.warn('failed: isValidChildAge new block could not be found');
    return false;
  }

  const headers = newBlock.getBlockchainHeaders().toObject();
  const newestHeader = Object.keys(headers).reduce((newest, key) => {
    const sorted = headers[key].sort((a, b) => {
      /* eslint-disable */
      if (new BN(a.timestamp).gt(new BN(b.timestamp)) === true) {
        return 1;
      }
      if (new BN(a.timestamp).lt(new BN(b.timestamp)) === true) {
        return -1;
      }
      return 0;
    });

    const header = sorted.pop();

    if (newest === false) {
      newest = header;
    } else {
      if (new BN(newest.timestamp).lt(new BN(header.timestamp))) {
        newest = header;
      }
    }
    return newest;
  }, false);

  if (newestHeader === false) {
    return false;
  }

  return newestHeader;
}

// function theBlockChainFingerPrintMatchGenesisBlock (newBlock: BcBlock): bool {
//  logger.info('theBlockChainFingerPrintMatchGenesisBlock validation running')
//  return newBlock.getBlockchainFingerprintsRoot() === GENESIS_DATA.blockchainFingerprintsRoot
// }

function numberOfBlockchainsNeededMatchesChildBlock(newBlock) {
  logger.debug('numberOfBlockchainsNeededMatchesChildBlock validation running');
  // skip for genesis block - it chas no blockchain blocks embedded
  if (newBlock.getHeight() === GENESIS_DATA.hash && newBlock.getHeight() === 1) {
    return true;
  }
  // verify that all blockain header lists are non empty and that there is childBlockchainCount of them
  const headerValues = Object.values(newBlock.getBlockchainHeaders().toObject());
  logger.debug(inspect(headerValues, { depth: 3 }));
  // $FlowFixMe
  const headerValuesWithLengthGtZero = headerValues.filter(headersList => headersList.length > 0);
  logger.debug(inspect(headerValuesWithLengthGtZero, { depth: 3 }));
  // logger.info(GENESIS_DATA.childBlockchainCount)
  return headerValuesWithLengthGtZero.length === GENESIS_DATA.childBlockchainCount;
}

function ifMoreThanOneHeaderPerBlockchainAreTheyOrdered(newBlock) {
  logger.debug('ifMoreThanOneHeaderPerBlockchainAreTheyOrdered validation running');
  const headersMap = newBlock.getBlockchainHeaders();

  // gather true/false for each chain signalling if either there is only one header
  // (most common case) or headers maintain ordering
  const chainsConditions = Object.keys(headersMap.toObject()).map(listName => {
    const getMethodName = `get${listName[0].toUpperCase()}${listName.slice(1)}`;
    const chainHeaders = headersMap[getMethodName]();
    if (chainHeaders.length === 1) {
      logger.debug(`ifMoreThanOneHeaderPerBlockchainAreTheyOrdered ${listName} single and valid`);
      return true;
    }

    // return true if left height < right height condition is valid
    // for all pairs ([[a, b], [b, c], [c, d]]) of chain headers ([a, b, c, d])
    // (in other words if ordering is maintained)
    // TODO
    const orderingCorrect = all(equals(true), aperture(2, chainHeaders).map(([a, b]) => a.getHeight() < b.getHeight()));
    logger.debug(`ifMoreThanOneHeaderPerBlockchainAreTheyOrdered ${listName} multiple and valid: ${orderingCorrect.toString()}`);
    if (!orderingCorrect) {
      logger.debug(`ifMoreThanOneHeaderPerBlockchainAreTheyOrdered ${inspect(headersMap.toObject())}`);
    }
    return orderingCorrect;
  });

  // check if all chain conditions are true
  logger.debug(`ifMoreThanOneHeaderPerBlockchainAreTheyOrdered all chain conditions: ${inspect(chainsConditions)}`);
  return all(equals(true), chainsConditions);
}

function isChainRootCorrectlyCalculated(newBlock) {
  logger.debug('isChainRootCorrectlyCalculated validation running');
  const receivedChainRoot = newBlock.getChainRoot();

  const expectedBlockHashes = getChildrenBlocksHashes(blockchainMapToList(newBlock.getBlockchainHeaders()));
  const expectedChainRoot = blake2bl(getChildrenRootHash(expectedBlockHashes).toString());
  return receivedChainRoot === expectedChainRoot;
}

function isFieldLengthBounded(newBlock) {
  logger.debug('isFieldLengthBounded validation running');
  return Object.keys(newBlock.toObject()).reduce((all, k) => {
    if (all[k] !== undefined && all[k].length > 128) {
      all = false;
    }
    return all;
  }, true);
}

function areDarkFibersValid(newBlock) {
  logger.debug('areDarkFibersValid validation running');
  const newBlockTimestampMs = newBlock.getTimestamp() * 1000;
  const blockchainHeadersList = blockchainMapToList(newBlock.getBlockchainHeaders());
  const dfBoundHeadersChecks = blockchainHeadersList.map(header => {
    // e.g. NEO 1000 (rovered ts)  <=    1400 (mined time) -   300 (dfBound for NEO)
    return header.getTimestamp() <= newBlockTimestampMs - DF_CONFIG[header.getBlockchain()].dfBound * 1000;
  });
  logger.debug(`dfBoundHeadersChecks: ${inspect(dfBoundHeadersChecks)}`);

  const dfVoidHeadersChecks = blockchainHeadersList.map(header => {
    const { dfVoid } = DF_CONFIG[header.getBlockchain()];
    return dfVoid === 0 || newBlockTimestampMs < header.getTimestamp() + dfVoid * 1000;
  });
  logger.debug(`dfVoidHeadersChecks: ${inspect(dfVoidHeadersChecks)}`);
  return all(equals(true), dfBoundHeadersChecks) && all(equals(true), dfVoidHeadersChecks);
}

function isMerkleRootCorrectlyCalculated(newBlock) {
  logger.debug('isMerkleRootCorrectlyCalculated validation running');
  const receivedMerkleRoot = newBlock.getMerkleRoot();

  const blockHashes = getChildrenBlocksHashes(blockchainMapToList(newBlock.getBlockchainHeaders()));
  const expectedMerkleRoot = createMerkleRoot(concatAll([blockHashes, newBlock.getTxsList(), [newBlock.getDifficulty(), newBlock.getMiner(), newBlock.getHeight(), newBlock.getVersion(), newBlock.getSchemaVersion(), newBlock.getNrgGrant(), GENESIS_DATA.blockchainFingerprintsRoot]]));

  return receivedMerkleRoot === expectedMerkleRoot;
}

function isDistanceAboveDifficulty(newBlock) {
  logger.debug('isDistanceCorrectlyCalculated validation running');
  const receivedDistance = newBlock.getDistance();
  const recievedDifficulty = newBlock.getDifficulty(); // !! NOTE: This is the difficulty for THIS block and not for the parent.
  logger.debug('receivedDistance ' + receivedDistance);
  logger.debug('receivedDifficulty ' + recievedDifficulty);

  return new BN(receivedDistance).gt(new BN(recievedDifficulty));
}

function isDistanceCorrectlyCalculated(newBlock) {
  logger.debug('isDistanceCorrectlyCalculated validation running');
  const receivedDistance = newBlock.getDistance();

  const expectedWork = prepareWork(newBlock.getPreviousHash(), newBlock.getBlockchainHeaders());
  const expectedDistance = distance(expectedWork, blake2bl(newBlock.getMiner() + newBlock.getMerkleRoot() + blake2bl(newBlock.getNonce()) + newBlock.getTimestamp())).toString();
  return receivedDistance === expectedDistance;
}

function blockchainHeadersAreChain(childHeaderList, parentHeaderList, block) {
  const firstChildHeader = head(childHeaderList);
  const lastParentHeader = last(parentHeaderList);

  // check if both parent and child have at least one header
  if (!firstChildHeader || !lastParentHeader) {
    const nonEmpty = firstChildHeader || lastParentHeader;
    if (nonEmpty) {
      logger.warn(`first child header or last parent header were empty for chain ${nonEmpty.getBlockchain()}`);
    } else {
      logger.warn(`both first child header and last parent header were missing`);
    }
    return false;
  }

  // check if either the header is the same one or first child header is actual child of last parent header
  let check = firstChildHeader.getPreviousHash() === lastParentHeader.getHash() || firstChildHeader.getHash() === lastParentHeader.getHash();

  if (!check) {
    logger.debug(`chain: "${firstChildHeader.getBlockchain()}" first child header ${inspect(firstChildHeader.toObject())} is not a child of last parent header ${inspect(lastParentHeader.toObject())}`);
    // return check // Disabled until AT
  }

  // if more than one child header check if child headers form a chain
  // if (childHeaderList.length > 1) {
  //  check = aperture(2, childHeaderList).reduce((result, [a, b]) => a.getHash() === b.getPreviousHash() && result, true)

  //  if (!check) {
  //    logger.info(`child headers do not form a chain`)
  //    // return check // Disabled until AT
  //  }
  // }

  // if more than one parent header check if parent headers form a chain
  if (parentHeaderList.length > 1) {
    check = aperture(2, parentHeaderList).reduce((result, [a, b]) => a.getHash() === b.getPreviousHash() && result, true);

    if (!check) {
      logger.debug(`parent headers do not form a chain`);
      // return check // Disabled until AT
    }
  }

  return true;
}

function validateRoveredSequences(blocks) {
  const sortedBlocks = sort((a, b) => b.getHeight() - a.getHeight(), blocks);
  const checks = aperture(2, sortedBlocks).map(([child, parent]) => {
    return parent.getHeight() === GENESIS_DATA.height || validateChildHeadersSequence(child, parent);
  });

  logger.debug(`validateRoveredSequences: ${inspect(checks)}`);

  return all(equals(true), flatten(checks));
}

function validateSequenceTotalDistance(previousBlock, newBlock) {
  logger.info('comparing totalDifficulties prevBlock: ' + previousBlock.getHeight() + ' with next block ' + newBlock.getHeight());

  const chainWeight = new BN(previousBlock.getDistance()).sub(new BN(previousBlock.getDifficulty())).divRound(new BN(8)).toString();
  //chainWeight = new BN(lastPreviousBlock.getDistance()).sub(new BN(previousBlock.getDifficulty())).divRound(new BN(8)).toString()

  // unfinishedBlock.setTotalDistance(new BN(unfinishedBlock.getTotalDistance()).add(new BN(chainWeight)).add(new BN(unfinishedBlock.getDifficulty(), 10)).toString())
  const finalDistance = new BN(previousBlock.getTotalDistance()).add(new BN(chainWeight)).add(new BN(newBlock.getDifficulty())).toString();

  logger.info('chain weight between prevBlock: ' + previousBlock.getHeight() + ' - ' + newBlock.getHeight() + ' is ' + chainWeight);
  logger.info('final total distance is ' + finalDistance);
  logger.info('final total distance should be ' + newBlock.getTotalDistance());

  if (previousBlock.getDifficulty() === "" || previousBlock.getDifficulty() < 1) {
    return true;
  }
  return finalDistance === newBlock.getTotalDistance();
}

function validateSequenceDifficulty(previousBlock, newBlock) {
  logger.info('comparing difficulties prevBlock: ' + previousBlock.getHeight() + ' with next block ' + newBlock.getHeight());
  const newBlockCount = getNewBlockCount(previousBlock.getBlockchainHeaders(), newBlock.getBlockchainHeaders());
  const preExpDiff = getDiff(newBlock.getTimestamp(), previousBlock.getTimestamp(), previousBlock.getDifficulty(), MINIMAL_DIFFICULTY, newBlockCount, getNewestHeader(newBlock));

  logger.info('preExpDiff: ' + preExpDiff);

  //const preExpDiff = getDiff(
  //  currentTimestamp,
  //  lastPreviousBlock.getTimestamp(),
  //  lastPreviousBlock.getDifficulty(),
  //  MINIMUM_DIFFICULTY,
  //  newBlockCount,
  //  getNewestHeader(lastPreviousBlock)
  //) // Calculate the final pre-singularity difficulty adjustment

  const finalDifficulty = getExpFactorDiff(preExpDiff, previousBlock.getHeight()).toString();

  logger.info('comparing difficulties prevBlock: ' + previousBlock.getHeight() + ' (' + previousBlock.getDifficulty() + ') with next block ' + newBlock.getHeight() + ' (' + newBlock.getDifficulty() + ') ');
  logger.info('difficulty should be ' + finalDifficulty);

  //if(previousBlock.getDifficulty() === "" || previousBlock.getDifficulty() < 1){
  //  logger.warn('difficulty assertion overridden
  //  return true
  //}
  return newBlock.getDifficulty() === finalDifficulty;
}

function validateChildHeadersSequence(childBlock, parentBlock) {
  const childBlockchainHeaders = childBlock.getBlockchainHeaders();
  const parentBlockchainHeaders = parentBlock.getBlockchainHeaders();
  // TODO this should be a map over all members of BlockchainHeaders instance to prevent error after adding another chain to Collider
  return [blockchainHeadersAreChain(childBlockchainHeaders.getBtcList(), parentBlockchainHeaders.getBtcList()), blockchainHeadersAreChain(childBlockchainHeaders.getEthList(), parentBlockchainHeaders.getEthList()), blockchainHeadersAreChain(childBlockchainHeaders.getLskList(), parentBlockchainHeaders.getLskList()), blockchainHeadersAreChain(childBlockchainHeaders.getNeoList(), parentBlockchainHeaders.getNeoList()), blockchainHeadersAreChain(childBlockchainHeaders.getWavList(), parentBlockchainHeaders.getWavList())];
}

function validateBlockSequence(blocks) {
  // if any of the submissions are undefined reject the sequence
  if (reject(identity, blocks).length > 0) {
    logger.debug('undefined members in set');
    return false;
  }
  // BC: 10 > BC: 9 > BC: 8 ...
  const sortedBlocks = sort((a, b) => b.getHeight() - a.getHeight(), blocks);
  const sortedBlocksTopDown = sort((a, b) => a.getHeight() - b.getHeight(), blocks);

  logger.debug(`validateBlockSequence sorted blocks ${sortedBlocks.map(b => b.getHeight()).toString()}`);
  // validate that Bc blocks are all in the same chain
  const validPairs = aperture(2, sortedBlocks).map(([a, b]) => {
    return a.getPreviousHash() === b.getHash();
  });

  logger.debug(`validateBlockSequence sorted blocks ${inspect(aperture(2, sortedBlocks.map(b => b.getHeight())))}`);
  if (!all(equals(true), validPairs)) {
    logger.debug(`validateBlockSequence validPairs: ${validPairs}`);
    return false;
  }

  /* eslint-disable */
  const validDifficulties = aperture(2, sortedBlocksTopDown).map(([a, b]) => {
    return validateSequenceDifficulty(a, b);
  });

  logger.debug(`validateBlockSequence sorted blocks ${inspect(aperture(2, sortedBlocks.map(b => b.getHeight())))}`);
  if (!all(equals(true), validDifficulties)) {
    logger.debug('validateBlockSequence invalid Difficulties');
    //return false
  }
  // validate that highest header from each blockchain list from each block maintains ordering
  // [[BC10, BC9], [BC9, BC8]]
  const pairs = aperture(2, sortedBlocks);
  const heights = pairs.map(a => {
    logger.debug(a);
    return [a[0].getHeight(), a[1].getHeight()];
  });
  logger.debug('pairs printed after this --> ' + JSON.stringify(heights, null, 2));
  // now create:
  // [[btcOrdered, ethOrdered, lskOrdered, neoOrdered, wavOrdered], [btcOrderder, ethOrdered, lskOrdered, neoOrdered, wavOrdered]]
  //                                e.g. BC10, BC9
  const validPairSubchains = pairs.map(([child, parent]) => {
    return parent.getHeight() === GENESIS_DATA.height || validateChildHeadersSequence(child, parent);
  });
  // flatten => [btc10_9Ordered, eth10_9Ordered, lsk10_9Ordered, neo10_9Ordered, wav10_9Ordered, btc9_8Orderded, eth9_8Ordered, lsk9_8Ordered, neo9_8Ordered, wav9_8Ordered]
  logger.debug(`validateBlockSequence validPairSubchains ${inspect(validPairSubchains)}`);
  if (!all(equals(true), flatten(validPairSubchains))) {
    logger.debug('failed test of rovers');
    // return false // TODO: AT -> is enabled in validation
  }

  return true;
}

function childrenHighestBlock(block) {

  const highest = Object.values(block.getBlockchainHeaders().toObject()).reduce((all, headers) => {
    const top = headers.sort((a, b) => {
      if (a.height > b.height) {
        return 1;
      }
      if (a.height < b.height) {
        return -1;
      }
      return 0;
    }).pop();
    if (top !== undefined) {
      all[top.blockchain] = top;
    }
    return all;
  }, {});

  const set = Object.values(highest);

  if (set.length < 1) {
    return [1];
  } else {
    return set;
  }
}

function childrenHeightSum(block) {
  return sum(childrenHighestBlock(block).map(header => Number(header.height)));
}
//# sourceMappingURL=validation.js.map
