structure vfmTestDefLib :> vfmTestDefLib = struct

  open HolKernel boolLib bossLib JSONDecode wordsLib cv_transLib
       vfmTestAuxLib vfmComputeTheory vfmTestRunTheory
       byteStringCacheLib vfmTypesSyntax vfmStateSyntax
       numSyntax stringSyntax listSyntax optionSyntax wordsSyntax fcpSyntax

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

  val storageDecoder : storage decoder =
    JSONDecode.map (List.map slot) rawObject

  val accountDecoder : account decoder =
    JSONDecode.map (fn (nonce, balance, code, storage) =>
                     {nonce=nonce, balance=balance,
                      code=code, storage=storage})
    (tuple4 (field "nonce" string, field "balance" string,
             field "code" string, field "storage" storageDecoder))

  val allocationDecoder : state decoder =
    JSONDecode.map
      (List.map
         (fn (k,v) => decode
           (JSONDecode.map (fn a => (k,a)) accountDecoder)
           v))
      rawObject

  val blobScheduleDecoder : blob_schedule decoder =
    JSONDecode.map (fn (t,m,f) => {target=t, max=m, base_fee_update_fraction=f})
    (tuple3 (field "target" string,
             field "max" string,
             field "base_fee_update_fraction" string))

  val accessListEntryDecoder : access_list_entry decoder =
    JSONDecode.map (fn (a,ks) => {address=a, storageKeys=ks})
      (tuple2 (field "address" string,
               field "storageKeys" (array string)))

  val accessListDecoder : access_list decoder = array accessListEntryDecoder

  val transactionDecoder : transaction decoder =
    JSONDecode.map (fn ((n,p,i,f),(l,t,v,d),(a,b,h,(sv,sr,ss,sa)),(ty,ci,k)) =>
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
    JSONDecode.map (fn (n,b) => {network=n, blobSchedule=b}) $
      tuple2 (field "network" string,
              try (field "blobSchedule" $
                   field fork_name blobScheduleDecoder))

  val blockHeaderDecoder : block_header decoder =
    JSONDecode.map (fn (((ph, uh, cb, sr), (tt, rt, bl, di),
                         (nu, gl, gu, ts), (ed, mh, no, ha)),
                        (bf, wr, bg, eb), pr) =>
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
    JSONDecode.map (fn (i,v,a,m) => {
               index=i, validatorIndex=v,
               address=a, amount=m}) $
      tuple4 (field "index" string,
              field "validatorIndex" string,
              field "address" string,
              field "amount" string)

  val blockDecoder : block decoder =
    JSONDecode.map (fn ((r,h,n),(t,u,w)) => {
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
    orElse (JSONDecode.map (fn (x,r,d) => Invalid {
                       expectException=x,
                       rlp=r,
                       rlp_decoded=d }) $
            tuple3 (field "expectException" string,
                    field "rlp" string,
                    try (field "rlp_decoded" blockDecoder)),
            JSONDecode.map Block blockDecoder)

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
          [bytes32_from_hex key,
           bytes32_from_hex value,
           mk_storage_tm_from_list ls])

  fun mk_account_tm ({balance, code, nonce, storage}: account) =
    TypeBase.mk_record(account_ty, [
      ("balance", num_from_hex balance),
      ("nonce", num_from_hex nonce),
      ("code", cached_bytes_from_hex code),
      ("storage", mk_storage_tm_from_list storage)
    ])


  fun mk_accounts_tm_from_list ([]: state) = empty_accounts_tm
    | mk_accounts_tm_from_list ((address,account)::ls) =
        list_mk_comb(update_account_tm,
          [address_from_hex address,
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
      ("account", address_from_hex address),
      ("keys", mk_list (List.map bytes32_from_hex storageKeys, bytes32_ty))
    ])

  fun mk_access_list_tm ls = mk_list(List.map mk_access_list_entry_tm ls,
                                     access_list_entry_ty)



  fun mk_transaction_tm baseFee_tm (tx: transaction) = let
    val to_tm = if #to tx = ""
                then optionSyntax.mk_none address_ty
                else optionSyntax.mk_some (address_from_hex (#to tx))
    val from_tm = address_from_hex (#sender tx)
    val data_tm = cached_bytes_from_hex $ #data tx
    val nonce_tm = num_from_hex $ #nonce tx
    val value_tm = num_from_hex $ #value tx
    val gasLimit_tm = num_from_hex $ #gasLimit tx
    val maxFeePerGas_tm = num_option_from_hex $ #maxFeePerGas tx
    val maxFeePerBlobGas_tm = num_option_from_hex $ #maxFeePerBlobGas tx
    val gasPrice_tm = case #gasPrice tx of
                           SOME s => num_from_hex s
                         | NONE => let
                                     val mno = num_from_hex o Option.valOf
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
                                        List.map bytes32_from_hex ls,
                                        bytes32_ty
                                      )
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
      ("maxFeePerGas", maxFeePerGas_tm),
      ("maxFeePerBlobGas", maxFeePerBlobGas_tm)
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
      ("withdrawalIndex", num_from_hex index),
      ("validatorIndex", num_from_hex validatorIndex),
      ("withdrawalAddress", address_from_hex address),
      ("withdrawalAmount", num_from_hex amount)])

  fun mk_block_tm (block: block) = let
    val header = #blockHeader block
    val baseFeePerGas_tm = num_from_hex $ #baseFeePerGas header
    val excessBlobGas_tm = num_from_hex $ #excessBlobGas header

    val gasUsed_tm = num_from_hex $ #gasUsed header
    val blobGasUsed_tm = num_from_hex $ #blobGasUsed header
    val number_tm = num_from_hex $ #number header
    val timeStamp_tm = num_from_hex $ #timestamp header
    val coinBase_tm = address_from_hex $ #coinbase header
    val gasLimit_tm = num_from_hex $ #gasLimit header
    val prevRandao_tm = bytes32_from_hex $ #mixHash header
    val hash_tm = bytes32_from_hex $ #hash header
    val stateRoot_tm = bytes32_from_hex $ #stateRoot header
    val parentBeaconBlockRoot_tm = bytes32_from_hex $ #parentBeaconBlockRoot header
    val transactions_tm = mk_list(
      List.map (mk_transaction_tm baseFeePerGas_tm) $
        #transactions block, transaction_ty)
    val withdrawals_tm = mk_list(
      List.map mk_withdrawal_tm $ #withdrawals block,
      withdrawal_ty)
  in
    TypeBase.mk_record(block_ty, [
      ("baseFeePerGas", baseFeePerGas_tm),
      ("excessBlobGas", excessBlobGas_tm),
      ("gasUsed", gasUsed_tm),
      ("blobGasUsed", blobGasUsed_tm),
      ("number", number_tm),
      ("timeStamp", timeStamp_tm),
      ("coinBase", coinBase_tm),
      ("gasLimit", gasLimit_tm),
      ("prevRandao", prevRandao_tm),
      ("hash", hash_tm),
      ("stateRoot", stateRoot_tm),
      ("parentBeaconBlockRoot", parentBeaconBlockRoot_tm),
      ("transactions", transactions_tm),
      ("withdrawals", withdrawals_tm)
    ])
  end

  val test_result_ty =
    mk_thy_type{Thy="vfmTestRun",Tyop="test_result",Args=[]}

  val run_test_tm =
    prim_mk_const{Thy="vfmTestRun",Name="run_test"}

  val optional_block_ty = optionSyntax.mk_option block_ty
  val invalid_block_ty = pairSyntax.mk_prod(bytes_ty, optional_block_ty)
  val expectException_ty = pairSyntax.mk_prod(string_ty, invalid_block_ty)

  fun is_invalid (Invalid _) = true | is_invalid _ = false
  fun dest_block (Block b) = b

  fun mk_genesis_block (rlp: string) (h: block_header) : block =
    {rlp = rlp, blockHeader = h, blocknumber = #number h,
     transactions = [], uncleHeaders = [], withdrawals = []}

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

    val g_rlp = #genesisRLP test
    val g_rlp_name = name_prefix ^ "_genesis_rlp"
    val g_rlp_var = mk_var(g_rlp_name, bytes_ty)
    val g_rlp_rhs = cached_bytes_from_hex g_rlp
    val g_rlp_def = new_definition(g_rlp_name ^ "_def",
                                   mk_eq(g_rlp_var, g_rlp_rhs))
    val g_rlp_const = lhs $ concl g_rlp_def
    val () = cv_trans g_rlp_def

    val g_block_name = name_prefix ^ "_genesis_block"
    val g_block_var = mk_var(g_block_name, block_ty)
    val g_block_rhs = mk_block_tm $ mk_genesis_block g_rlp
                                  $ #genesisBlockHeader test
    val g_block_def = new_definition(g_block_name ^ "_def",
                                    mk_eq(g_block_var, g_block_rhs))
    val g_block_const = lhs $ concl g_block_def
    val () = cv_trans g_block_def

    val last_hash_name = name_prefix ^ "_last_hash"
    val last_hash_var = mk_var(last_hash_name, bytes32_ty)
    val last_hash_rhs = bytes32_from_hex $ #lastblockhash test
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
           cached_bytes_from_hex
           (optionSyntax.lift_option optional_block_ty mk_block_tm))
        expectException

    val validBlocks = List.map dest_block (
      if Option.isSome expectException
      then List.take(boris, last_index)
      else boris )
    val validBlocks_tm = listSyntax.mk_list(
      List.map mk_block_tm validBlocks, block_ty)

    val rlps_tms = List.map (cached_bytes_from_hex o #rlp) validBlocks
    val rlps_name = name_prefix ^ "_rlps"
    val rlps_var = mk_var(rlps_name, listSyntax.mk_list_type bytes_ty)
    val rlps_rhs = listSyntax.mk_list(rlps_tms, bytes_ty)
    val rlps_def = new_definition(rlps_name ^ "_def",
                                  mk_eq(rlps_var, rlps_rhs))
    val rlps_const = lhs $ concl rlps_def
    val () = cv_trans rlps_def

    val blocks_name = name_prefix ^ "_blocks"
    val blocks_var = mk_var(blocks_name, listSyntax.mk_list_type block_ty)
    val blocks_def = new_definition(blocks_name ^ "_def",
                                    mk_eq(blocks_var, validBlocks_tm))
    val blocks_const = lhs $ concl blocks_def
    val () = cv_trans blocks_def

    val result_name = name_prefix ^ "_result"
    val result_var = mk_var(result_name, test_result_ty)
    val result_rhs = list_mk_comb(run_test_tm, [
      pre_const, g_rlp_const, g_block_const,
      blocks_const, rlps_const, last_hash_const, post_state_const,
      expectException_tm])
    val result_def = new_definition(result_name ^ "_def",
                                    mk_eq(result_var, result_rhs))
  in
    result_def
  end

end
