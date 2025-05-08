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
             tuple4 (try (field "accessList" accessListDecoder),
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
                    orElse (field "withdrawals" (array withdrawalDecoder),
                            succeed [])))

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

  fun mk_cached_bytes_tm str = let
  val hex = if String.isPrefix "0x" str
                then trim2 str else str in
  case Redblackmap.peek(!bytestr_cache, hex)
    of SOME const => const | NONE =>
  let
    val n = Redblackmap.numItems $ !bytestr_cache
    val name = String.concat["bytestr_", Int.toString n]
    val var = mk_var(name, bytes_ty)
    val rhs_tm = mk_hex_to_rev_bytes_tm_from_string hex
    val def = new_definition(name ^ "_def", mk_eq(var, rhs_tm))
    val () = cv_trans_deep_embedding EVAL def
    val const = lhs (concl def)
    val cache = Redblackmap.insert(!bytestr_cache, hex, const)
    val () = bytestr_cache := cache
  in const end
  end

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

  val withdrawal_ty =
    mk_thy_type{Thy="vfmContext",Tyop="withdrawal",Args=[]}

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
      ("code", mk_cached_bytes_tm code),
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

  fun mk_transaction_tm baseFee_tm (tx: transaction) = let
    val to_tm = if #to tx = ""
                then optionSyntax.mk_none address_ty
                else optionSyntax.mk_some (mk_address_tm (#to tx))
    val from_tm = mk_address_tm (#sender tx)
    val data_tm = mk_cached_bytes_tm $ #data tx
    val nonce_tm = mk_num_tm $ #nonce tx
    val value_tm = mk_num_tm $ #value tx
    val gasLimit_tm = mk_num_tm $ #gasLimit tx
    val gasPrice_tm = case #gasPrice tx of
                           SOME s => mk_num_tm s
                         | NONE => let
                                     val mno = mk_num_tm o Option.valOf
                                     val maxFee_tm = mno $ #maxFeePerGas tx
                                     val prioFee_tm = mno $ #maxPriorityFeePerGas tx
                                   in
                                     list_mk_comb(effective_gas_price_tm,
                                       [baseFee_tm, maxFee_tm, prioFee_tm])
                                   end
    val accessList_tm = case #accessList tx of
                             NONE => empty_access_list_tm
                           | SOME ls => mk_access_list_tm ls
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

  fun mk_withdrawal_tm {index, validatorIndex, address, amount} =
    TypeBase.mk_record(withdrawal_ty, [
      ("withdrawalIndex", mk_num_tm index),
      ("validatorIndex", mk_num_tm validatorIndex),
      ("withdrawalAddress", mk_address_tm address),
      ("withdrawalAmount", mk_num_tm amount)])

  fun mk_block_tm (block: block) = let
    val header = #blockHeader block
    val baseFeePerGas_tm = mk_num_tm $ #baseFeePerGas header
    val number_tm = mk_num_tm $ #number header
    val timeStamp_tm = mk_num_tm $ #timestamp header
    val coinBase_tm = mk_address_tm $ #coinbase header
    val gasLimit_tm = mk_num_tm $ #gasLimit header
    val prevRandao_tm = mk_bytes32_tm $ #mixHash header
    val hash_tm = mk_bytes32_tm $ #hash header
    val parentBeaconBlockRoot_tm = mk_bytes32_tm $ #parentBeaconBlockRoot header
    val transactions_tm = mk_list(
      List.map (mk_transaction_tm baseFeePerGas_tm) $
        #transactions block, transaction_ty)
    val withdrawals_tm = mk_list(
      List.map mk_withdrawal_tm $ #withdrawals block,
      withdrawal_ty)
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
      ("transactions", transactions_tm),
      ("withdrawals", withdrawals_tm)
    ])
  end

  val test_result_ty =
    mk_thy_type{Thy="vfmTestHelper",Tyop="test_result",Args=[]}

  val run_test_tm =
    prim_mk_const{Thy="vfmTestHelper",Name="run_test"}

  val fuel_tm = numSyntax.term_of_int state_root_fuel

  val optional_block_ty = optionSyntax.mk_option block_ty
  val invalid_block_ty = pairSyntax.mk_prod(bytes_ty, optional_block_ty)
  val expectException_ty = pairSyntax.mk_prod(string_ty, invalid_block_ty)

  fun is_invalid (Invalid _) = true | is_invalid _ = false
  fun dest_block (Block b) = b

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
    val post_state_rhs = mk_accounts_tm_from_list (#post test)
    val post_state_def = new_definition(post_state_name ^ "_def",
                                        mk_eq(post_state_var, post_state_rhs))
    val post_state_const = lhs $ concl post_state_def
    val () = cv_trans post_state_def

    val g_rlp_name = name_prefix ^ "_genesis_rlp"
    val g_rlp_var = mk_var(g_rlp_name, bytes_ty)
    val g_rlp_rhs = mk_cached_bytes_tm $ #genesisRLP test
    val g_rlp_def = new_definition(g_rlp_name ^ "_def",
                                   mk_eq(g_rlp_var, g_rlp_rhs))
    val g_rlp_const = lhs $ concl g_rlp_def
    val () = cv_trans g_rlp_def

    val g_root_name = name_prefix ^ "_genesis_root"
    val g_root_var = mk_var(g_root_name, bytes32_ty)
    val g_root_rhs = mk_bytes32_tm $ #stateRoot $ #genesisBlockHeader test
    val g_root_def = new_definition(g_root_name ^ "_def",
                                    mk_eq(g_root_var, g_root_rhs))
    val g_root_const = lhs $ concl g_root_def
    val () = cv_trans_deep_embedding EVAL g_root_def

    val g_hash_name = name_prefix ^ "_genesis_hash"
    val g_hash_var = mk_var(g_hash_name, bytes32_ty)
    val g_hash_rhs = mk_bytes32_tm $ #hash $ #genesisBlockHeader test
    val g_hash_def = new_definition(g_hash_name ^ "_def",
                                    mk_eq(g_hash_var, g_hash_rhs))
    val g_hash_const = lhs $ concl g_hash_def
    val () = cv_trans_deep_embedding EVAL g_hash_def

    val last_hash_name = name_prefix ^ "_last_hash"
    val last_hash_var = mk_var(last_hash_name, bytes32_ty)
    val last_hash_rhs = mk_bytes32_tm $ #lastblockhash test
    val last_hash_def = new_definition(last_hash_name ^ "_def",
                                    mk_eq(last_hash_var, last_hash_rhs))
    val last_hash_const = lhs $ concl last_hash_def
    val () = cv_trans_deep_embedding EVAL last_hash_def

    val boris = #blocks test
    val last_index = List.length boris - 1
    val expectException =
      if List.exists is_invalid boris
      then if List.exists is_invalid (List.take(boris, last_index))
           then raise Fail "invalid block not the last block"
           else case List.nth(boris, last_index)
                of Invalid {expectException, rlp, rlp_decoded} =>
                   SOME (expectException, (rlp, rlp_decoded))
      else NONE
    val expectException_tm =
      optionSyntax.lift_option
        (optionSyntax.mk_option expectException_ty)
        (pairSyntax.lift_prod expectException_ty fromMLstring $
         pairSyntax.lift_prod invalid_block_ty
           mk_cached_bytes_tm
           (optionSyntax.lift_option optional_block_ty mk_block_tm))
        expectException

    val validBlocks = List.map dest_block (
      if Option.isSome expectException
      then List.take(boris, last_index)
      else boris )
    val validBlocks_tm = listSyntax.mk_list(
      List.map mk_block_tm validBlocks, block_ty)
    val blocks_name = name_prefix ^ "_blocks"
    val blocks_var = mk_var(blocks_name, listSyntax.mk_list_type block_ty)
    val blocks_def = new_definition(blocks_name ^ "_def",
                                    mk_eq(blocks_var, validBlocks_tm))
    val blocks_const = lhs $ concl blocks_def
    val () = cv_trans blocks_def

    val result_name = name_prefix ^ "_result"
    val result_var = mk_var(result_name, test_result_ty)
    val result_rhs = list_mk_comb(run_test_tm, [
      fuel_tm, pre_const,
      g_rlp_const, g_root_const, g_hash_const,
      blocks_const, last_hash_const, post_state_const,
      expectException_tm])
    val result_def = new_definition(result_name ^ "_def",
                                    mk_eq(result_var, result_rhs))
  in
    result_def
  end

end
