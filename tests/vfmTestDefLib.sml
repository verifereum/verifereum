structure vfmTestDefLib :> vfmTestDefLib = struct

  open HolKernel boolLib bossLib JSONDecode wordsLib cv_transLib
       vfmTestAuxLib vfmComputeTheory vfmTestHelperTheory
       numSyntax stringSyntax listSyntax wordsSyntax fcpSyntax

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
    withdrawals: withdrawal list option
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

  val transactionDecoder : transaction decoder =
    andThen (fn ((n,p,i,f),(l,t,v,d),(a,b,h,(sv,sr,ss,sa)),(ty,ci,k)) => succeed
      {nonce=n, gasPrice=p, maxPriorityFeePerGas=i, maxFeePerGas=f,
       gasLimit=l, to=t, value=v, data=d, accessList=a, maxFeePerBlobGas=b,
       r=sr, s=ss, v=sv,
       blobVersionedHashes=h, sender=sa, secretKey=k, txtype=ty, chainId=ci})
    (tuple4 (tuple4 (field "nonce" string,
                     try (field "gasPrice" string),
                     try (field "maxPriorityFeePerGas" string),
                     try (field "maxFeePerGas" string)),
             tuple4 (field "gasLimit" string,
                     field "to" string,
                     field "value" string,
                     field "data" string),
             tuple4 (try (field "accessLists" accessListDecoder),
                     try (field "maxFeePerBlobGas" string),
                     try (field "blobVersionedHashes" (array string)),
                     tuple4 (field "v" string,
                             field "r" string,
                             field "s" string,
                             field "sender" string)),
             tuple3 (field "type" string,
                     field "chainId" string,
                     orElse (field "secretKey" string, succeed ""))))

  val configDecoder : config decoder =
    andThen (fn (n,b) => succeed {network=n, blobSchedule=b}) $
      tuple2 (field "network" string,
              try (field "blobSchedule" $
                   field fork_name blobScheduleDecoder))

  val blockHeaderDecoder : block_header decoder =
    andThen (fn (((ph, uh, cb, sr), (tt, rt, bl, di),
                  (nu, gl, gu, ts), (ed, mh, no, ha)),
                 (bf, wr, bg, eb), pr) => succeed $
              {parentHash=ph, uncleHash=uh, coinbase=cb, stateRoot=sr,
               transactionsTrie=tt, receiptTrie=rt, bloom=bl, difficulty=di,
               number=nu, gasLimit=gl, gasUsed=gu, timestamp=ts,
               extraData=ed, mixHash=mh, nonce=no, hash=ha,
               baseFeePerGas=bf, withdrawalsRoot=wr, blobGasUsed=bg,
               excessBlobGas=eb, parentBeaconBlockRoot=pr}) $
      tuple3 (
        tuple4 (tuple4 (field "parentHash" string,
                        field "uncleHash" string,
                        field "coinbase" string,
                        field "stateRoot" string),
                tuple4 (field "transactionsTrie" string,
                        field "receiptTrie" string,
                        field "bloom" string,
                        field "difficulty" string),
                tuple4 (field "number" string,
                        field "gasLimit" string,
                        field "gasUsed" string,
                        field "timestamp" string),
                tuple4 (field "extraData" string,
                        field "mixHash" string,
                        field "nonce" string,
                        field "hash" string)),
        tuple4 (field "baseFeePerGas" string,
                field "withdrawalsRoot" string,
                field "blobGasUsed" string,
                field "excessBlobGas" string),
        field "parentBeaconBlockRoot" string)

  val withdrawalDecoder : withdrawal decoder =
    andThen (fn (i,v,a,m) => succeed {
               index=i, validatorIndex=v,
               address=a, amount=m}) $
      tuple4 (field "index" string,
              field "validatorIndex" string,
              field "address" string,
              field "amount" string)

  val blockDecoder : block decoder =
    andThen (fn ((r,h,n),(t,u,w)) => succeed {
               rlp=r, blockHeader=h, blocknumber=n,
               transactions=t, uncleHeaders=u, withdrawals=w}) $
    tuple2 (tuple3 (orElse (field "rlp" string, succeed ""),
                    field "blockHeader" blockHeaderDecoder,
                    field "blocknumber" string),
            tuple3 (field "transactions" (array transactionDecoder),
                    field "uncleHeaders" (array blockHeaderDecoder),
                    try (field "withdrawals" (array withdrawalDecoder))))

  val blockOrInvalidDecoder : block_or_invalid decoder =
    orElse (andThen (fn (x,r,d) => succeed $ Invalid {
                       expectException=x,
                       rlp=r,
                       rlp_decoded=d }) $
            tuple3 (field "expectException" string,
                    field "rlp" string,
                    try (field "rlp_decoded" blockDecoder)),
            andThen (succeed o Block) blockDecoder)

  fun test_fixture_to_test (fixture_name, fixture) : test option = let
    val config = decode (field "config" configDecoder) fixture
  in if #network config <> fork_name then NONE else let
    val pre = decode (field "pre" allocationDecoder) fixture
    val genesisRLP = decode (field "genesisRLP" string) fixture
    val genesisBlockHeader = decode
      (field "genesisBlockHeader" blockHeaderDecoder) fixture
    val blocks = decode (field "blocks" (array blockOrInvalidDecoder)) fixture
    val lastblockhash = decode (field "lastblockhash" string) fixture
    val post = decode (orElse (field "post" allocationDecoder,
                               field "postState" allocationDecoder)) fixture
  in
    SOME $ {
      name=fixture_name,
      pre=pre,
      genesisRLP=genesisRLP,
      genesisBlockHeader=genesisBlockHeader,
      blocks=blocks,
      lastblockhash=lastblockhash,
      post=post,
      config=config
    }
  end end

  val json_path_to_tests =
    decodeFile (JSONDecode.map (List.mapPartial test_fixture_to_test) rawObject)

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

  val run_test_tm =
    prim_mk_const{Thy="vfmTestHelper",Name="run_test"}

  val fuel_tm = numSyntax.term_of_int state_root_fuel

  fun define_test range_prefix test_number (test: test) = let
    val name_prefix = String.concat ["test_", range_prefix, "_", Int.toString test_number]

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
    val result_rhs = list_mk_comb(run_test_tm, [
      fuel_tm, exec_const, pre_const, expectException_tm,
      lhs(concl post_hash_def), lhs(concl logs_hash_def)])
    val result_def = new_definition(result_name ^ "_def",
                                    mk_eq(result_var, result_rhs))
  in
    result_def
  end

end
