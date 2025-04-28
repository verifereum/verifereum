structure vfmTestLib = struct
  open HolKernel JSONDecode vfmContextTheory
       stringSyntax wordsSyntax fcpSyntax

  fun front n = (curry $ flip List.take) n
  val trim2 = Substring.string o Substring.triml 2 o Substring.full

  val fork_name = "Cancun"

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

  fun collect_json_files path (dirs, jsons) = let
    val ds = OS.FileSys.openDir path
    fun loop (dirs, jsons) =
      case OS.FileSys.readDir ds of
           NONE => (dirs, jsons)
         | SOME file => loop let
             val pf = OS.Path.concat (path, file)
           in
             if OS.Path.ext file = SOME "json"
             then (dirs, pf::jsons)
             else if OS.FileSys.isDir pf
             then (pf::dirs, jsons)
             else (dirs, jsons)
           end
  in
    loop (dirs, jsons)
    before OS.FileSys.closeDir ds
  end

  fun collect_json_files_rec start_path = let
    fun loop [] jsons = jsons
      | loop (path::paths_left) jsons = let
          val (dirs, jsons) = collect_json_files path (paths_left, jsons)
        in loop dirs jsons end
  in
    loop [start_path] []
  end

  fun slot (k,v) : slot = {key=k, value=decode string v}

  val storageDecoder : storage decoder = andThen
    (fn ls => succeed (List.map slot ls))
    rawObject

  val accountDecoder : account decoder =
    andThen (fn (nonce, balance, code, storage) =>
             succeed {nonce=nonce, balance=balance,
                      code=code, storage=storage})
    (tuple4 (field "nonce" string, field "balance" string,
             field "code" string, field "storage" storageDecoder))

  val allocationDecoder : state decoder =
    andThen
      (succeed o List.map
         (fn (k,v) => decode
           (JSONDecode.map (fn a => (k,a)) accountDecoder)
           v))
      rawObject

  val envDecoder : env decoder =
    andThen (fn ((coinbase, gasLimit, number, difficulty),
                 (timestamp, baseFee, random, excessBlobGas)) =>
              succeed
              {coinbase=coinbase, gasLimit=gasLimit, number=number,
               difficulty=difficulty, timestamp=timestamp, baseFee=baseFee,
               random=random, excessBlobGas=excessBlobGas})
      (tuple2 (tuple4 (field "currentCoinbase" string, field "currentGasLimit" string,
                       field "currentNumber" string, field "currentDifficulty" string),
               tuple4 (field "currentTimestamp" string,
                       try (field "currentBaseFee" string),
                       try (field "currentRandom" string),
                       try (field "currentExcessBlobGas" string))))

  val indexesDecoder : indexes decoder =
    andThen (fn (d,g,v) => succeed {data=d, gas=g, value=v})
      (tuple3 (field "data" int, field "gas" int, field "value" int))

  val postDecoder : post decoder =
    andThen (fn (i,(t,h,l),e,s) => succeed
               {indexes=i, txbytes=t, hash=h, logs=l,
                expectException=e, state=s})
      (tuple4 (field "indexes" indexesDecoder,
               tuple3 (field "txbytes" string,
                       field "hash" string,
                       field "logs" string),
               try (field "expectException" string),
               field "state" allocationDecoder))

  val blobScheduleDecoder : blob_schedule decoder =
    andThen (fn (t,m,f) => succeed
      {target=t, max=m, base_fee_update_fraction=f})
    (tuple3 (field "target" string,
             field "max" string,
             field "base_fee_update_fraction" string))

  val accessListEntryDecoder : access_list_entry decoder =
    andThen (fn (a,ks) => succeed {address=a, storageKeys=ks})
      (tuple2 (field "address" string,
               field "storageKeys" (array string)))

  val accessListDecoder : access_list decoder = array accessListEntryDecoder

  val indexedTransactionDecoder : indexed_transaction decoder =
    andThen (fn ((n,p,i,f),(l,t,v,d),(a,b,h,s),k) => succeed
      {nonce=n, gasPrice=p, maxPriorityFeePerGas=i, maxFeePerGas=f,
       gasLimit=l, to=t, value=v, data=d, accessList=a, maxFeePerBlobGas=b,
       blobVersionedHashes=h, sender=s, secretKey=k})
    (tuple4 (tuple4 (field "nonce" string,
                     try (field "gasPrice" string),
                     try (field "maxPriorityFeePerGas" string),
                     try (field "maxFeePerGas" string)),
             tuple4 (field "gasLimit" (array string),
                     field "to" string,
                     field "value" (array string),
                     field "data" (array string)),
             tuple4 (try (field "accessLists" (array accessListDecoder)),
                     try (field "maxFeePerBlobGas" string),
                     try (field "blobVersionedHashes" (array string)),
                     field "sender" string),
             field "secretKey" string))

  fun state_test_fixture_to_test (fixture_name, fixture) : state_test option = let
    val pre = decode (field "pre" allocationDecoder) fixture
    val env = decode (field "env" envDecoder) fixture
    val posts = decode (field "post"
      (orElse (field fork_name (array postDecoder),
               succeed []))) fixture
    val [post] = if List.length posts > 1
                 then raise Fail ("non-deterministic test: " ^ fixture_name)
                 else posts
    val tx = decode (field "transaction" indexedTransactionDecoder) fixture
    val bs = decode (field "config" (try (field fork_name blobScheduleDecoder))) fixture
  in
    SOME $
    {name=fixture_name,
     pre=pre, env=env, post=post,
     transaction=tx,
     blobSchedule=bs}
  end handle Bind => NONE

  val state_test_json_to_tests =
    decodeFile (JSONDecode.map (List.mapPartial state_test_fixture_to_test) rawObject)

  fun get_first_n_state_tests n =
    "fixtures/state_tests"
    |> collect_json_files_rec
    |> front n
    |> List.map state_test_json_to_tests
    |> List.concat
    |> front n

  val test_number = 2
  val [_,_,test] = get_first_n_state_tests 3

  val address_bits_ty = mk_int_numeric_type 160
  val bytes32_bits_ty = mk_int_numeric_type 256
  val address_ty = mk_word_type address_bits_ty
  val bytes32_ty = mk_word_type bytes32_bits_ty
  val account_ty = mk_thy_type{Thy="vfmState",Tyop="account_state", Args=[]}
  val accounts_ty = address_ty --> account_ty

  val byte_ty = mk_word_type (mk_int_numeric_type 8)
  val bytes_ty = listSyntax.mk_list_type byte_ty

  val string_ty = string_ty

  val hex_to_rev_bytes_tm =
    mk_thy_const{Name="hex_to_rev_bytes",Thy="keccak",
                 Ty=bytes_ty --> string_ty --> bytes_ty}

  fun mk_hex_to_rev_bytes_tm_from_string str =
    listSyntax.mk_reverse(
      list_mk_comb(hex_to_rev_bytes_tm,
        [listSyntax.mk_nil byte_ty,
         fromMLstring str]))

  val mk_num_tm = numSyntax.mk_numeral o Arbnum.fromHexString

  fun mk_bytes32_tm hex = mk_n2w(mk_num_tm hex, bytes32_bits_ty)
  fun mk_address_tm hex = mk_n2w(mk_num_tm hex, address_bits_ty)

  val storage_ty = bytes32_ty --> bytes32_ty
  val empty_storage_tm =
    mk_thy_const{Name="empty_storage",Thy="vfmState",Ty=storage_ty}
  val update_storage_tm =
    mk_thy_const{Name="update_storage",Thy="vfmState",
                 Ty=bytes32_ty --> bytes32_ty --> storage_ty --> storage_ty}

  val empty_accounts_tm =
    mk_thy_const{Name="empty_accounts",Thy="vfmState",Ty=accounts_ty}
  val update_account_tm =
    mk_thy_const{Name="update_account",Thy="vfmState",
                 Ty=address_ty --> account_ty --> accounts_ty --> accounts_ty}

  fun mk_storage_tm_from_list ([]: slot list) = empty_storage_tm
    | mk_storage_tm_from_list ({key,value}::ls) =
        list_mk_comb(update_storage_tm,
          [mk_bytes32_tm key,
           mk_bytes32_tm value,
           mk_storage_tm_from_list ls])

  fun mk_account_tm ({balance, code, nonce, storage}: account) =
    TypeBase.mk_record(account_ty, [
      ("balance", mk_num_tm balance),
      ("nonce", mk_num_tm nonce),
      ("code", mk_hex_to_rev_bytes_tm_from_string (trim2 code)),
      ("storage", mk_storage_tm_from_list storage)
    ])

  fun mk_accounts_tm_from_list ([]: state) = empty_accounts_tm
    | mk_accounts_tm_from_list ((address,account)::ls) =
        list_mk_comb(update_account_tm,
          [mk_address_tm address,
           mk_account_tm account,
           mk_accounts_tm_from_list ls])

  fun make_state_test_definitions test_number test = let
    val name_prefix = String.concat ["state_test_", Int.toString test_number]
    val pre_name = String.concat [name_prefix, "_pre"]
    val pre_var = mk_var(pre_name, accounts_ty)
    val pre_rhs = mk_accounts_tm_from_list pre
    val pre_def = new_definition(pre_name ^ "_def", mk_eq(pre_var, pre_rhs))
  in
    pre_def (* TODO: return the final test definition etc. *)
  end

  (*
    Treat each of these separately:
    1. State tests
       a. Pick test naming scheme, maybe numbered
          with actual name as a string constant?
       b. Define components of test as HOL constants (produce theory with these
          definitions)
       c. CV-translate these constants, using caching and deep embeddings where
          appropriate (produce theory with these translations, could be same as
          above)
       d. Define HOL function that checks a state test following the consumption
          instructions, and cv-translate it.
       e. cv-eval test-checking function on all the tests (produce theory that
          includes these theorems for passing tests, and reports on failing tests
          too)
    2. Blockchain tests
    3. Legacy state tests (General State Tests ?)
    4. Legacy blockchain tests
    Ignoring for now: Blockchain engine tests, Transaction tests, (other) Legacy tests
  *)
end
