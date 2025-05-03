signature vfmTestLib = sig

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

  type env = {
    coinbase: string,
    gasLimit: string,
    number: string,
    difficulty: string,
    timestamp: string,
    baseFee: string option,
    random: string option,
    excessBlobGas: string option
  }

  type indexes = {
    data: int,
    gas: int,
    value: int
  }

  type post = {
    indexes: indexes,
    txbytes: string,
    hash: string,
    logs: string,
    expectException: string option,
    state: state
  }

  type indexed_transaction = {
    nonce: string,
    gasPrice: string option,
    maxPriorityFeePerGas: string option,
    maxFeePerGas: string option,
    gasLimit: string list,
    to: string,
    value: string list,
    data: string list,
    accessList: access_list list option,
    maxFeePerBlobGas: string option,
    blobVersionedHashes: string list option,
    sender: string,
    secretKey: string
  }

  type blob_schedule = {
    target: string,
    max: string,
    base_fee_update_fraction: string
  }

  type state_test = {
    name: string,
    pre: state,
    env: env,
    transaction: indexed_transaction,
    post: post,
    blobSchedule: blob_schedule option
  }

  val get_all_state_test_json_paths : unit -> string list
  val state_test_json_path_to_tests : string -> state_test list

  val generate_state_test_defn_scripts : unit -> unit

  val define_state_test : string -> int -> state_test -> Thm.thm
  val define_state_tests : int -> int -> Thm.thm list

  val get_result_defs : string -> (string * Thm.thm) list
  val save_result_thm : Time.time -> (string * Thm.thm) -> Thm.thm
  val default_limit : Time.time

  val export_theory_no_docs: unit -> unit

end
