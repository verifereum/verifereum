structure readTestJsonLib = struct
  open HolKernel

  val jq_path = "/usr/bin/jq";

  fun run_jq args = let
    val proc = Unix.execute(jq_path, args)
  in
    TextIO.inputAll $ Unix.textInstreamOf proc
    before ignore $ Unix.reap proc
  end

  fun unquote s = String.substring(s, 1, String.size s - 2)

  fun trimws s = Substring.full s
    |> Substring.dropl Char.isSpace
    |> Substring.dropr Char.isSpace
    |> Substring.string

  fun unlist s = String.tokens(equal #",")(unquote s)

  fun strls s = s |> trimws |> unlist |> List.map unquote
  fun num s = s |> trimws |> Int.fromString |> Option.valOf

  fun get_test_names json_path =
    run_jq ["-rcM", "keys", json_path] |> strls

  fun get_test json_path test_name = let
    fun rjq a = run_jq $ ["-rcM"] @ a @ [json_path]
    val tt = "." ^ test_name
    val nblocks = rjq [tt ^ ".blocks | length"] |> num
    val ntxns = rjq [tt ^ ".blocks[0].transactions | length"] |> num
    val () = if nblocks <> 1 orelse ntxns <> 1
             then raise Fail "only 1 transaction in 1 block currently supported"
             else ()
    val bk = tt ^ ".blocks[0]"
    val bh = bk ^ ".blockHeader"
    val bhkeys = rjq [bh ^ " | keys"] |> strls
    val () = if List.exists (String.isSuffix "andao") bhkeys
             then raise Fail "Unexpected key (looks like randao) in blockheader"
             else ()
    val number = rjq [bh ^ ".number"] |> trimws
    val hash = rjq [bh ^ ".hash"] |> trimws
    val blockGasLimit = rjq [bh ^ ".gasLimit"] |> trimws
    val baseFeePerGas = rjq [bh ^ ".baseFeePerGas"] |> trimws
    val prevRandao = rjq [bh ^ ".mixHash"] |> trimws
    val parentBeaconBlockRoot = rjq [bh ^ ".parentBeaconBlockRoot"] |> trimws
    val timeStamp = rjq [bh ^ ".timestamp"] |> trimws
    val coinBase = rjq [bh ^ ".coinbase"] |> trimws
    val tx = bk ^ ".transactions[0]"
    val data = rjq [tx ^ ".data"] |> trimws
    val gasLimit = rjq [tx ^ ".gasLimit"] |> trimws
    val gasPrice = rjq [tx ^ ".gasPrice"] |> trimws
    val nonce = rjq [tx ^ ".nonce"] |> trimws
    val sender = rjq [tx ^ ".sender"] |> trimws
    val to = rjq [tx ^ ".to"] |> trimws
    val value = rjq [tx ^ ".value"] |> trimws
    val postKeys = rjq [tt ^ ".postState | keys"] |> strls
    val preKeys = rjq [tt ^ ".pre | keys"] |> strls
    val () = if
      List.exists (String.isPrefix "access") (rjq [tx ^ " | keys"] |> strls)
    then raise Fail "accessList not yet supported" else ()
    fun get_account st addr = let
      val a = tt ^ st ^ ".[\"" ^ addr ^ "\"]"
      val balance = rjq [a ^ ".balance"] |> trimws
      val code = rjq [a ^ ".code"] |> trimws
      val nonce = rjq [a ^ ".nonce"] |> trimws
      val storageKeys = rjq [a ^ ".storage | keys"] |> strls
      fun getSlot k = {key=k, value=rjq [a ^ ".storage.[\"" ^ k ^ "\"]"] |> trimws}
      val storage = List.map getSlot storageKeys
    in
      {address=addr, balance=balance, code=code, nonce=nonce, storage=storage}
    end
    val post = List.map (get_account ".postState") postKeys
    val pre = List.map (get_account ".pre") preKeys
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
      nonce=nonce,
      sender=sender,
      to=to,
      value=value
    }
  in
    {block=block, transaction=transaction, pre=pre, post=post}
  end

  (*
    val json_path = "tests/add.json"
    val test_names = get_test_names json_path
    val test_name = el 2 test_names
    val test2 = get_test json_path test_name
  *)

end
