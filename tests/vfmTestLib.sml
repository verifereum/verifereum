structure vfmTestLib :> vfmTestLib = struct
  open HolKernel boolLib bossLib JSONDecode wordsLib cv_transLib
  vfmContextTheory vfmComputeTheory vfmTestHelperTheory
  numSyntax stringSyntax listSyntax wordsSyntax fcpSyntax

  fun ss f = Substring.string o f o Substring.full
  fun trimr n = ss $ Substring.trimr n
  fun triml n = ss $ Substring.triml n
  val trim2 = triml 2

  fun padl n z s = let
    val m = String.size s
  in
    if m < n
    then (String.implode (List.tabulate(n-m, K z))) ^ s
    else s
  end

  val export_theory_no_docs = fn () =>
    Feedback.set_trace "TheoryPP.include_docs" 0
    before export_theory ()

  val fork_name = "Cancun"
  val chain_id = 1

  val state_root_fuel = 1024
  val default_limit = Time.fromSeconds 60;

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

  fun collect_files suffix path (dirs, files) = let
    val ds = OS.FileSys.openDir path
    fun loop (dirs, files) =
      case OS.FileSys.readDir ds of
           NONE => (dirs, files)
         | SOME file => loop let
             val pf = OS.Path.concat (path, file)
           in
             if OS.Path.ext file = SOME suffix
             then (dirs, pf::files)
             else if OS.FileSys.isDir pf
             then (pf::dirs, files)
             else (dirs, files)
           end
  in
    loop (dirs, files)
    before OS.FileSys.closeDir ds
  end

  val collect_json_files = collect_files "json"

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

  val state_test_json_path_to_tests =
    decodeFile (JSONDecode.map (List.mapPartial state_test_fixture_to_test) rawObject)

  fun get_all_state_test_json_paths () =
    "fixtures/state_tests"
    |> collect_json_files_rec

  val address_bits_ty = mk_int_numeric_type 160
  val bytes32_bits_ty = mk_int_numeric_type 256
  val address_ty = mk_word_type address_bits_ty
  val bytes32_ty = mk_word_type bytes32_bits_ty
  val account_ty = mk_thy_type{Thy="vfmState",Tyop="account_state", Args=[]}
  val accounts_ty = address_ty --> account_ty

  val byte_ty = mk_word_type (mk_int_numeric_type 8)
  val bytes_ty = mk_list_type byte_ty

  val hex_to_rev_bytes_tm =
    mk_thy_const{Name="hex_to_rev_bytes",Thy="keccak",
                 Ty=bytes_ty --> string_ty --> bytes_ty}

  fun mk_hex_to_rev_bytes_tm_from_string str =
    mk_reverse(
      list_mk_comb(hex_to_rev_bytes_tm,
        [mk_nil byte_ty,
         fromMLstring str]))

  val bytestr_cache : (string, term) Redblackmap.dict ref =
    ref $ Redblackmap.mkDict String.compare

  fun mk_cached_bytes_tm str =
    case Redblackmap.peek(!bytestr_cache, str)
      of SOME const => const | NONE =>
  let
    val n = Redblackmap.numItems $ !bytestr_cache
    val name = String.concat["bytestr_", Int.toString n]
    val var = mk_var(name, bytes_ty)
    val rhs_tm = mk_hex_to_rev_bytes_tm_from_string str
    val def = new_definition(name ^ "_def", mk_eq(var, rhs_tm))
    val () = cv_trans_deep_embedding EVAL def
    val const = lhs (concl def)
    val cache = Redblackmap.insert(!bytestr_cache, str, const)
    val () = bytestr_cache := cache
  in const end

  val mk_num_tm = numSyntax.mk_numeral o Arbnum.fromHexString

  fun mk_bytes32_tm hex = mk_n2w(mk_num_tm hex, bytes32_bits_ty)
  fun mk_address_tm hex = mk_n2w(mk_num_tm hex, address_bits_ty)

  val zero_bytes32 = mk_n2w(numSyntax.zero_tm, bytes32_bits_ty)

  val storage_ty = bytes32_ty --> bytes32_ty
  val empty_storage_tm =
    mk_thy_const{Name="empty_storage",Thy="vfmState",Ty=storage_ty}
  val update_storage_tm =
    mk_thy_const{Name="update_storage",Thy="vfmState",
                 Ty=bytes32_ty --> bytes32_ty --> storage_ty --> storage_ty}

  val transaction_ty =
    mk_thy_type{Thy="vfmTransaction",Tyop="transaction",Args=[]}

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
      ("code", mk_cached_bytes_tm (trim2 code)),
      ("storage", mk_storage_tm_from_list storage)
    ])

  fun mk_accounts_tm_from_list ([]: state) = empty_accounts_tm
    | mk_accounts_tm_from_list ((address,account)::ls) =
        list_mk_comb(update_account_tm,
          [mk_address_tm address,
           mk_account_tm account,
           mk_accounts_tm_from_list ls])

  val effective_gas_price_tm =
    mk_thy_const{Name="effective_gas_price",Thy="vfmTransaction",
                 Ty=num --> num --> num --> num}

  val access_list_entry_ty =
    mk_thy_type{Thy="vfmTransaction",Tyop="access_list_entry",Args=[]}
  val access_list_ty = mk_list_type access_list_entry_ty
  val empty_access_list_tm = mk_nil access_list_entry_ty

  fun mk_access_list_entry_tm ({address, storageKeys}: access_list_entry) =
    TypeBase.mk_record(access_list_entry_ty, [
      ("account", mk_address_tm address),
      ("keys", mk_list (List.map mk_bytes32_tm storageKeys, bytes32_ty))
    ])

  fun mk_access_list_tm ls = mk_list(List.map mk_access_list_entry_tm ls,
                                     access_list_entry_ty)

  fun mk_transaction_tm (env: env) (ix: indexes) (tx: indexed_transaction) = let
    val {data=di, gas=gi, value=vi} = ix
    val to_tm = if #to tx = ""
                then optionSyntax.mk_none address_ty
                else optionSyntax.mk_some (mk_address_tm (#to tx))
    val from_tm = mk_address_tm (#sender tx)
    val data_tm = mk_cached_bytes_tm $
                    trim2(List.nth(#data tx, di))
    val nonce_tm = mk_num_tm (#nonce tx)
    val value_tm = mk_num_tm (List.nth(#value tx, vi))
    val gasLimit_tm = mk_num_tm (List.nth(#gasLimit tx, gi))
    val gasPrice_tm = case #gasPrice tx of
                           SOME s => mk_num_tm s
                         | NONE => let
                                     val mno = mk_num_tm o Option.valOf
                                     val baseFee_tm = mno $ #baseFee $ env
                                     val maxFee_tm = mno $ #maxFeePerGas tx
                                     val prioFee_tm = mno $ #maxPriorityFeePerGas tx
                                   in
                                     list_mk_comb(effective_gas_price_tm,
                                       [baseFee_tm, maxFee_tm, prioFee_tm])
                                   end
    val accessList_tm = case #accessList tx of
                             NONE => empty_access_list_tm
                           | SOME ls => mk_access_list_tm $ List.nth(ls, di)
    val blobVersionedHashes_tm = case #blobVersionedHashes tx of
                                      NONE => mk_nil bytes32_ty
                                    | SOME ls => mk_list(
                                        List.map mk_bytes32_tm ls,
                                        bytes32_ty
                                      )
    val blobGasPrice_tm = mk_num_tm "0" (* TODO: calculate blob gas price from
    excess env? or maybe this doesn't actually need to be on the transaction *)
  in
    TypeBase.mk_record(transaction_ty, [
      ("to", to_tm),
      ("from", from_tm),
      ("data", data_tm),
      ("nonce", nonce_tm),
      ("value", value_tm),
      ("gasLimit", gasLimit_tm),
      ("gasPrice", gasPrice_tm),
      ("accessList", accessList_tm),
      ("blobVersionedHashes", blobVersionedHashes_tm),
      ("blobGasPrice", blobGasPrice_tm)
    ])
  end

  val domain_ty = mk_thy_type{Thy="vfmContext",Tyop="domain",Args=[]}
  val domain_mode_ty = mk_thy_type{Thy="vfmContext",Tyop="domain_mode",Args=[]}
  val Collect_tm =
    mk_thy_const{Thy="vfmContext",Name="Collect",Ty=domain_ty --> domain_mode_ty}
  val empty_domain_tm =
    mk_thy_const{Thy="vfmContext",Name="empty_domain",Ty=domain_ty}
  val Collect_empty_dom_tm = mk_comb(Collect_tm, empty_domain_tm)

  val block_ty = mk_thy_type{Thy="vfmContext",Tyop="block",Args=[]}

  val run_block_tm =
    prim_mk_const{Thy="vfmExecution",Name="run_block"}

  val run_block_result_ty = #2 $ strip_fun $ type_of run_block_tm

  val run_blocks_tm =
    prim_mk_const{Thy="vfmExecution",Name="run_blocks"}

  val run_transaction_tm =
    prim_mk_const{Thy="vfmExecution",Name="run_transaction"}

  val run_transaction_result_ty = #2 $ strip_fun $ type_of run_transaction_tm

  val chain_id_tm = numSyntax.term_of_int chain_id

  fun mk_block_tm (env: env) (tx: term) = let
    val baseFeePerGas_tm = case #baseFee env of NONE => zero_tm
                              | SOME s => mk_num_tm s
    val number_tm = mk_num_tm $ #number env
    val timeStamp_tm = mk_num_tm $ #timestamp env
    val coinBase_tm = mk_address_tm $ #coinbase env
    val gasLimit_tm = mk_num_tm $ #gasLimit env
    val prevRandao_tm = case #random env of NONE => zero_bytes32
                           | SOME s => mk_bytes32_tm s
    val hash_tm = zero_bytes32 (* not used in state tests *)
    val parentBeaconBlockRoot_tm = zero_bytes32 (* ditto *)
    val transactions_tm = mk_list([tx], transaction_ty)
  in
    TypeBase.mk_record(block_ty, [
      ("baseFeePerGas", baseFeePerGas_tm),
      ("number", number_tm),
      ("timeStamp", timeStamp_tm),
      ("coinBase", coinBase_tm),
      ("gasLimit", gasLimit_tm),
      ("prevRandao", prevRandao_tm),
      ("hash", hash_tm),
      ("parentBeaconBlockRoot", parentBeaconBlockRoot_tm),
      ("transactions", transactions_tm)
    ])
  end

  val test_result_ty =
    mk_thy_type{Thy="vfmTestHelper",Tyop="test_result",Args=[]}

  val run_state_test_tm =
    prim_mk_const{Thy="vfmTestHelper",Name="run_state_test"}

  val fuel_tm = numSyntax.term_of_int state_root_fuel

  fun define_state_test range_prefix test_number (test: state_test) = let
    val name_prefix = String.concat ["state_test_", range_prefix, "_", Int.toString test_number]

    val name_name = name_prefix ^ "_name"
    val name_var = mk_var(name_name, string_ty)
    val name_def = new_definition(name_name ^ "_def",
                                  mk_eq(name_var, fromMLstring (#name test)))

    val pre_name = String.concat [name_prefix, "_pre_state"]
    val pre_var = mk_var(pre_name, accounts_ty)
    val pre_rhs = mk_accounts_tm_from_list (#pre test)
    val pre_def = new_definition(pre_name ^ "_def", mk_eq(pre_var, pre_rhs))
    val pre_const = lhs (concl pre_def)
    val () = cv_trans pre_def

    val post_state_name = name_prefix ^ "_post_state"
    val post_state_var = mk_var(post_state_name, accounts_ty)
    val post_state_rhs = mk_accounts_tm_from_list (#state (#post test))
    val post_state_def = new_definition(post_state_name ^ "_def",
                                        mk_eq(post_state_var, post_state_rhs))
    (* not needed - do it on demand when debugging
    val () = cv_trans post_state_def
    *)

    val post_hash_name = name_prefix ^ "_post_hash"
    val post_hash_var = mk_var(post_hash_name, bytes32_ty)
    val post_hash_rhs = mk_bytes32_tm (#hash (#post test))
    val post_hash_def = new_definition(post_hash_name ^ "_def",
                                       mk_eq(post_hash_var, post_hash_rhs))
    val () = cv_trans_deep_embedding EVAL post_hash_def

    val logs_hash_name = name_prefix ^ "_logs_hash"
    val logs_hash_var = mk_var(logs_hash_name, bytes32_ty)
    val logs_hash_rhs = mk_bytes32_tm (#logs (#post test))
    val logs_hash_def = new_definition(logs_hash_name ^ "_def",
                                       mk_eq(logs_hash_var, logs_hash_rhs))
    val () = cv_trans_deep_embedding EVAL logs_hash_def

    val txbytes_name = name_prefix ^ "_txbytes"
    val txbytes_var = mk_var(txbytes_name, bytes_ty)
    val txbytes_rhs = mk_hex_to_rev_bytes_tm_from_string $
                        trim2 (#txbytes (#post test))
    val txbytes_def = new_definition(txbytes_name ^ "_def",
                                     mk_eq(txbytes_var, txbytes_rhs))
    val () = cv_trans_deep_embedding EVAL txbytes_def

    val env = #env test
    val tx_name = name_prefix ^ "_transaction"
    val tx_var = mk_var(tx_name, transaction_ty)
    val tx_rhs = mk_transaction_tm env
                   (#indexes (#post test)) (#transaction test)
    val tx_def = new_definition(tx_name ^ "_def", mk_eq(tx_var, tx_rhs))
    val tx_const = lhs (concl tx_def)
    val () = cv_trans tx_def

    val expectException = #expectException (#post test)
    val expectException_tm = expectException |>
      optionSyntax.lift_option
        (optionSyntax.mk_option string_ty)
        fromMLstring

    val block_name = name_prefix ^ "_block"
    val block_var = mk_var(block_name, block_ty)
    val block_rhs = mk_block_tm env tx_const
    val block_def = new_definition(block_name ^ "_def",
                                   mk_eq(block_var, block_rhs))
    val block_const = lhs (concl block_def)
    val () = cv_trans block_def

    val prevHashes_tm = mk_nil bytes32_ty

    val exec_name = name_prefix ^ "_exec"
    val exec_var = mk_var(exec_name, run_transaction_result_ty)
    val exec_rhs = list_mk_comb(run_transaction_tm,
      [Collect_empty_dom_tm, F, chain_id_tm, prevHashes_tm,
       block_const, pre_const, tx_const])
    val exec_def = new_definition(exec_name ^ "_def", mk_eq(exec_var, exec_rhs))
    val exec_const = lhs (concl exec_def)
    val () = cv_trans exec_def

    val result_name = name_prefix ^ "_result"
    val result_var = mk_var(result_name, test_result_ty)
    val result_rhs = list_mk_comb(run_state_test_tm, [
      fuel_tm, exec_const, pre_const, expectException_tm,
      lhs(concl post_hash_def), lhs(concl logs_hash_def)])
    val result_def = new_definition(result_name ^ "_def",
                                    mk_eq(result_var, result_rhs))
  in
    result_def
  end

  fun state_test_defn_script_text index json_path = let
    val sidx = padl 3 #"0" $ Int.toString index
    val thyn = "vfmStateTestDefs" ^ sidx
    val text = String.concat [
      "open HolKernel vfmTestLib;\n",
      "val () = new_theory \"", thyn, "\";\n",
      "val tests = state_test_json_path_to_tests \"../../", json_path, "\";\n",
      "val defs = mapi (define_state_test \"", sidx, "\") tests;\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (thyn, text)
  end

  fun state_test_result_script_text thyn = let
    val z = String.size thyn
    val rthy = Substring.concat [
                  Substring.substring(thyn, 0, 12),
                  Substring.substring(thyn, z-3, 3)
               ]
    val text = String.concat [
      "open HolKernel vfmTestLib ", thyn, "Theory; \n",
      "val () = new_theory \"", rthy, "\";\n",
      "val () = List.app (ignore o save_result_thm default_limit) $ ",
      "get_result_defs \"", thyn, "\";\n",
      "val () = export_theory_no_docs ();\n"
    ]
  in
    (rthy, text)
  end

  fun write_script dir (thyn, text) = let
    val path = dir ^ thyn ^ "Script.sml"
    val out = TextIO.openOut path
    val () = TextIO.output (out, text)
  in
    TextIO.closeOut out
  end

  fun generate_state_test_defn_scripts () = let
    val json_paths = get_all_state_test_json_paths ()
    val named_scripts = mapi state_test_defn_script_text json_paths
  in
    List.app (write_script "state/defs/") named_scripts
  end

  fun generate_state_test_result_scripts () = let
    val (_, smls) = collect_files "sml" "state/defs" ([], [])
    val scripts = List.filter (String.isSuffix "Script.sml") smls
    val thyns = List.map (ss (Substring.triml 11 o Substring.trimr 10)) smls
    val named_scripts = List.map state_test_result_script_text thyns
  in
    List.app (write_script "state/results/") named_scripts
  end

  fun define_state_tests range_start range_length = let
    val all_json_paths = get_all_state_test_json_paths ();
    val json_paths = List.drop(all_json_paths, range_start)
    val paths_in_range = if range_length < List.length json_paths
                         then List.take(json_paths, range_length)
                         else json_paths
    val tests = List.concat (List.map state_test_json_path_to_tests paths_in_range)
  in
    mapi (define_state_test (Int.toString range_start)) tests
  end

  val get_result_defs =
    List.filter (String.isSuffix "result_def" o #1) o
    definitions

  val eval_rhs = CONV_RULE $ RAND_CONV cv_eval;

  fun save_result_thm limit (result_def_name, result_def) = let
    val result_name = trimr 4 result_def_name
    val () = Feedback.HOL_MESG $ String.concat ["Evaluating ", result_name]
    val start_time = Time.now()
    val result_eval = Timeout.apply limit eval_rhs result_def
    val end_time = Time.now()
    val () = Feedback.HOL_MESG $ String.concat $ [
               thm_to_string result_eval,
               " (", Time.fmt 2 $ end_time - start_time, "s)"
             ]
  in
    save_thm(result_name, result_eval)
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
