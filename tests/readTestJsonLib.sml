structure readTestJsonLib = struct
  open HolKernel JSONDecode

  val ERR = Feedback.mk_HOL_ERR "readTestJsonLib"

  val get_test_names =
    decodeFile $ JSONDecode.map (List.map fst) rawObject

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
    val bhkeys = decode rawObject bh |> List.map fst
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

    val postState = getObject tobj "postState"
    val postStateHash = getObject tobj "postStateHash" |> Option.map getString'
    val preState = getObject' tobj "pre"

    val postKeys = Option.map getKeys' postState
    val preKeys = getKeys' preState

    fun get_account state addr = let
        val a = getObject' state addr
        val balance = getObject' a "balance" |> getString'
        val code = getObject' a "code" |> getString'
        val nonce = getObject' a "nonce" |> getString'
        fun getSlots slots =
            case slots of
                AList slots' => List.map (fn (k,v) =>
                                             { key= k, value= getString' v}) slots'
              | _ => raise ERR "get_account" "expect an object"

      val storage = getObject' a "storage" |> getSlots
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

  (*
    val json_path = test_path
    val test_names = get_test_names json_path
    val test_name = el 1 test_names
    val test2 = get_test json_path test_name
  *)

end
