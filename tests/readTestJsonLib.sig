signature readTestJsonLib = sig
  val get_test_names : string -> string list

  type access_list_entry = {address: string, storageKeys: string list}
  type access_list = access_list_entry list

  type transaction = {
    data: string,
    gasLimit: string,
    gasPrice: string option,
    maxFeePerGas: string option,
    maxPriorityFeePerGas: string option,
    nonce: string,
    sender: string,
    to: string,
    value: string,
    accessList: access_list
  }

  type block = {
    number: string,
    hash: string,
    parentHash: string,
    gasLimit: string,
    baseFeePerGas: string,
    prevRandao: string,
    parentBeaconBlockRoot: string,
    timeStamp: string,
    coinBase: string,
    transactions: transaction list
  }

  type slot = {
    key: string,
    value: string
  }

  type account = {
    address: string,
    balance: string,
    code: string,
    nonce: string,
    storage: slot list
  }

  type state = account list

  type test = {
    blocks: block list,
    pre: state,
    post: state option,
    postHash: string option
  }

  val get_test : string -> string -> test
end
