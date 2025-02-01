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

  fun getBlockHeader' block =
    case getObject block "blockHeader" of
      SOME h => h
    | NONE => getObject' block "rlp_decoded"
              |> C getObject' "blockHeader"

  fun get_test json_path test_name = let
    val (json, rest) = Json.fromFile json_path
    val tobj = Json.getObject' (hd json) test_name
    val blocks = Json.getObject' tobj "blocks" |> getArray'

    val nblocks = blocks |> length
    val block0 = hd blocks
    val txns = getTransactions' block0
    val ntxns = length txns
    val () = if nblocks <> 1 orelse ntxns <> 1
             then raise Fail "only 1 transaction in 1 block currently supported"
             else ()

    val bh0 = getBlockHeader' block0
    val bhkeys = bh0 |> getKeys'
    val () = if List.exists (String.isSuffix "andao") bhkeys
             then raise Fail "Unexpected key (looks like randao) in blockheader"
             else ()

    val number = getObject' bh0 "number" |> getString'
    val hash = getObject' bh0 "hash" |> getString'
    val blockGasLimit = getObject' bh0 "gasLimit" |> getString'
    val baseFeePerGas = getObject' bh0 "baseFeePerGas" |> getString'
    val prevRandao = getObject' bh0 "mixHash" |> getString'
    val parentBeaconBlockRoot = getObject' bh0 "parentBeaconBlockRoot" |> getString'
    val timeStamp = getObject' bh0 "timestamp" |> getString'
    val coinBase = getObject' bh0 "coinbase" |> getString'

    val tx0 = hd txns

    val data = getObject' tx0 "data" |> getString'
    val gasLimit = getObject' tx0 "gasLimit" |> getString'
    val gasPrice = getObject tx0 "gasPrice" |> Option.map getString'
    val maxFeePerGas = getObject tx0 "maxFeePerGas" |> Option.map getString'
    val maxPriorityFeePerGas = getObject tx0 "maxPriorityFeePerGas" |> Option.map getString'
    val nonce = getObject' tx0 "nonce" |> getString'
    val sender = getObject' tx0 "sender" |> getString'
    val to = getObject' tx0 "to" |> getString'
    val value = getObject' tx0 "value" |> getString'
    val accessList = getObject tx0 "accessList" |> getAccessList'

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
    val block = {
      number=number,
      hash=hash,
      gasLimit=blockGasLimit,
      baseFeePerGas=baseFeePerGas,
      prevRandao=prevRandao,
      parentBeaconBlockRoot=parentBeaconBlockRoot,
      timeStamp=timeStamp,
      coinBase=coinBase
    }
    val transaction = {
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
  in
    {block=block, transaction=transaction, pre=pre, post=post,
     postHash=postStateHash}
  end

  (*
    val json_path = test_path
    val test_names = get_test_names json_path
    val test_name = el 1 test_names
    val test2 = get_test json_path test_name
  *)

end
