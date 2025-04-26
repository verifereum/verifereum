structure readTestJsonLib :> readTestJsonLib = struct
  open HolKernel JSONDecode

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

  val keysDecoder = JSONDecode.map (List.map fst) rawObject

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

  val get_test_names = decodeFile keysDecoder

  fun decodeAccessList NONE = []
    | decodeAccessList (SOME j) = decode
      (array (andThen (fn address =>
              andThen (fn storageKeys =>
                succeed {address=address, storageKeys=storageKeys})
              (field "storageKeys" (array string)))
              (field "address" string)))
      j

  fun decodeTransaction tx = let
    fun dt d = decode d tx
    val data = dt $ field "data" string
    val gasLimit = dt $ field "gasLimit" string
    val gasPrice = dt $ try $ field "gasPrice" string
    val maxFeePerGas = dt $ try $ field "maxFeePerGas" string
    val maxPriorityFeePerGas = dt $ try $ field "maxPriorityFeePerGas" string
    val nonce = dt $ field "nonce" string
    val sender = dt $ field "sender" string
    val to = dt $ field "to" string
    val value = dt $ field "value" string
    val rawAccessList = dt $ try $ field "accessList" raw
    val accessList = decodeAccessList rawAccessList
  in {
      data=data,
      gasLimit=gasLimit,
      gasPrice=gasPrice,
      maxFeePerGas=maxFeePerGas,
      maxPriorityFeePerGas=maxPriorityFeePerGas,
      nonce=nonce,
      sender=sender,
      to=to,
      value=value,
      accessList=accessList
    }
  end

  fun fieldOrRlpDecoded k d =
    orElse (field k d, field "rlp_decoded" (field k d))

  fun decodeBlock b = let
    val bh = decode (fieldOrRlpDecoded "blockHeader" raw) b
    val bhkeys = decode keysDecoder bh
    val () = if List.exists (String.isSuffix "andao") bhkeys
             then raise Fail "Unexpected key (looks like randao) in blockheader"
             else ()
    val number = decode (field "number" string) bh
    val hash = decode (field "hash" string) bh
    val parentHash = decode (field "parentHash" string) bh
    val blockGasLimit = decode (field "gasLimit" string) bh
    val baseFeePerGas = decode (field "baseFeePerGas" string) bh
    val prevRandao = decode (field "mixHash" string) bh
    val parentBeaconBlockRoot = decode (field "parentBeaconBlockRoot" string) bh
    val timeStamp = decode (field "timestamp" string) bh
    val coinBase = decode (field "coinbase" string) bh
    val rawTransactions = decode (fieldOrRlpDecoded "transactions" (array raw)) b
    val transactions = List.map decodeTransaction rawTransactions
  in {
      number=number,
      hash=hash,
      parentHash=parentHash,
      gasLimit=blockGasLimit,
      baseFeePerGas=baseFeePerGas,
      prevRandao=prevRandao,
      parentBeaconBlockRoot=parentBeaconBlockRoot,
      timeStamp=timeStamp,
      coinBase=coinBase,
      transactions=transactions
    }
  end

  fun get_test json_path test_name = let
    val tobj = decodeFile (field test_name raw) json_path
    fun dt d = decode d tobj

    val rawBlocks = dt (field "blocks" (array raw))
    val blocks = List.map decodeBlock rawBlocks

    val postState = dt (try (field "postState" raw))
    val postStateHash = dt (try (field "postStateHash" string))
    val preState = dt (field "pre" raw)

    val postKeys = Option.map (decode keysDecoder) postState
    val preKeys = decode keysDecoder preState

    fun get_account state addr = let
        val a = decode (field addr raw) state
        val balance = decode (field "balance" string) a
        val code = decode (field "code" string) a
        val nonce = decode (field "nonce" string) a
        val rawStorage = decode (field "storage" rawObject) a
        fun slot (k,v) = {key=k, value=decode string v}
        val storage = List.map slot rawStorage
    in
      {address=addr, balance=balance, code=code, nonce=nonce, storage=storage}
    end

    val post = Option.map (fn keys =>
                 List.map (get_account (Option.valOf postState)) keys
               ) postKeys
    val pre = List.map (get_account preState) preKeys
  in
    {blocks=blocks, pre=pre, post=post, postHash=postStateHash}
  end

  val fork_name = "Cancun"

  fun slot (k,v) = {key=k, value=decode string v}

  val storageDecoder = andThen
    (fn ls => succeed (List.map slot ls))
    rawObject

  fun accountDecoder address : account decoder =
    andThen (fn (nonce, balance, code, storage) =>
             succeed {address=address, nonce=nonce,
                      balance=balance, code=code,
                      storage=storage})
    (tuple4 (field "nonce" string, field "balance" string,
             field "code" string, field "storage" storageDecoder))

  val allocationDecoder =
    andThen
      (succeed o List.map
         (fn (k,v) => decode (accountDecoder k) v))
      rawObject

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

  type state_test = {
    name: string,
    pre: account list,
    env: env,
    transaction: indexed_transaction,
    post: post,
    blobSchedule: blob_schedule option
  }

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

  fun get_all_state_tests () =
    "fixtures/state_tests"
    |> collect_json_files_rec
    |> List.map state_test_json_to_tests
    |> List.concat

  (*
    Treat each of these separately:
    1. State tests
    2. Blockchain tests
    3. Legacy state tests (General State Tests ?)
    4. Legacy blockchain tests
    Ignoring for now: Blockchain engine tests, Transaction tests, (other) Legacy tests



    val blockchain_jsons = collect_json_files_rec "fixtures/blockchain_tests"
    val state_jsons = collect_json_files_rec "fixtures/state_tests"
    val transaction_jsons = collect_json_files_rec "fixtures/transaction_tests"
    val json_path = el 1 state_jsons

    val fallarcs = List.map (#arcs o OS.Path.fromString) fallj
    val btallj = collect_json_files_rec "tests/BlockchainTests"
    val gsallj = collect_json_files_rec "tests/GeneralStateTests"
    val eallj = collect_json_files_rec "tests/EIPTests"
    val test_name = el 1 fallarcs |> last |> OS.Path.base

    (JSONDecode.map (#2 o el test_index)) rawObject

    val json_path = test_path
    val test_names = get_test_names json_path
    val test_name = el 1 test_names
    val test2 = get_test json_path test_name
  *)
end
