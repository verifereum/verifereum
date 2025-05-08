signature vfmTestDefLib = sig

  type access_list_entry = {address: string, storageKeys: string list}
  type access_list = access_list_entry list

  type slot = {key: string, value: string}
  type storage = slot list

  type account = {
    balance: string,
    code: string,
    nonce: string,
    storage: storage
  }

  type state = (string * account) list

  type transaction = {
    txtype: string,
    chainId: string,
    nonce: string,
    gasPrice: string option,
    maxPriorityFeePerGas: string option,
    maxFeePerGas: string option,
    gasLimit: string,
    to: string,
    value: string,
    data: string,
    accessList: access_list option,
    maxFeePerBlobGas: string option,
    blobVersionedHashes: string list option,
    v: string,
    r: string,
    s: string,
    sender: string,
    secretKey: string
  }

  type blob_schedule = {
    target: string,
    max: string,
    base_fee_update_fraction: string
  }

  type config = {
    network: string,
    blobSchedule: blob_schedule option
  }

  type block_header = {
    parentHash: string,
    uncleHash: string,
    coinbase: string,
    stateRoot: string,
    transactionsTrie: string,
    receiptTrie: string,
    bloom: string,
    difficulty: string,
    number: string,
    gasLimit: string,
    gasUsed: string,
    timestamp: string,
    extraData: string,
    mixHash: string,
    nonce: string,
    hash: string,
    baseFeePerGas: string,
    withdrawalsRoot: string,
    blobGasUsed: string,
    excessBlobGas: string,
    parentBeaconBlockRoot: string
  }

  type withdrawal = {
    index: string,
    validatorIndex: string,
    address: string,
    amount: string
  }

  type block = {
    rlp: string,
    blockHeader: block_header,
    blocknumber: string,
    transactions: transaction list,
    uncleHeaders: block_header list,
    withdrawals: withdrawal list
  }

  type invalid_block = {
    expectException: string,
    rlp: string,
    rlp_decoded: block option
  }

  datatype block_or_invalid = Block of block | Invalid of invalid_block

  type test = {
    name: string,
    pre: state,
    genesisRLP: string,
    genesisBlockHeader: block_header,
    blocks: block_or_invalid list,
    lastblockhash: string,
    post: state,
    config: config
  }

  val json_path_to_tests : string -> test list

  val define_test : string -> int -> test -> Thm.thm

end
