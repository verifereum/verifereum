structure readTestJsonLib = struct
  open HolKernel Json

  val ERR = Feedback.mk_HOL_ERR "readTestJsonLib"

  fun get_test_names json_path = let
      val (json, rest) = Json.fromFile json_path
  in
      Json.getKeys' (hd json)
  end

(* TODO: Move into examples/json *)
  fun getArray' u =
      case u of
          Json.List u => u
        | _ => raise ERR "getArray'" "expect an associated list"

  fun getAccessListEntry j = let
    val address = getObject' j "address" |> getString'
    val storageKeys = getObject' j "storageKeys" |> getArray' |> List.map getString'
  in
    {address=address, storageKeys=storageKeys}
  end

  fun getAccessList' NONE = []
    | getAccessList' (SOME j) = getArray' j |> List.map getAccessListEntry

  fun getTransactions' block =
    case getObject block "transactions" of
      SOME txns => getArray' txns
    | NONE => getObject' block "rlp_decoded"
              |> C getObject' "transactions"
              |> getArray'

  fun getTransaction tx = let
    val data = getObject' tx "data" |> getString'
    val gasLimit = getObject' tx "gasLimit" |> getString'
    val gasPrice = getObject tx "gasPrice" |> Option.map getString'
    val maxFeePerGas = getObject tx "maxFeePerGas" |> Option.map getString'
    val maxPriorityFeePerGas = getObject tx "maxPriorityFeePerGas" |> Option.map getString'
    val nonce = getObject' tx "nonce" |> getString'
    val sender = getObject' tx "sender" |> getString'
    val to = getObject' tx "to" |> getString'
    val value = getObject' tx "value" |> getString'
    val accessList = getObject tx "accessList" |> getAccessList'

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


  fun getTransactions'' block = getTransactions' block |> List.map
    getTransaction

  fun getBlockHeader' block =
    case getObject block "blockHeader" of
      SOME h => h
    | NONE => getObject' block "rlp_decoded"
              |> C getObject' "blockHeader"

  fun getBlock' block = let
    val bh0 = getBlockHeader' block
    val bhkeys = bh0 |> getKeys'
    val () = if List.exists (String.isSuffix "andao") bhkeys
             then raise Fail "Unexpected key (looks like randao) in blockheader"
             else ()

    val number = getObject' bh0 "number" |> getString'
    val hash = getObject' bh0 "hash" |> getString'
    val parentHash = getObject' bh0 "parentHash" |> getString'
    val blockGasLimit = getObject' bh0 "gasLimit" |> getString'
    val baseFeePerGas = getObject' bh0 "baseFeePerGas" |> getString'
    val prevRandao = getObject' bh0 "mixHash" |> getString'
    val parentBeaconBlockRoot = getObject' bh0 "parentBeaconBlockRoot" |> getString'
    val timeStamp = getObject' bh0 "timestamp" |> getString'
    val coinBase = getObject' bh0 "coinbase" |> getString'
    val transactions = getTransactions'' block
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
    val (json, rest) = Json.fromFile json_path
    val tobj = Json.getObject' (hd json) test_name
    val blocks = Json.getObject' tobj "blocks" |> getArray' |> map getBlock'

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
