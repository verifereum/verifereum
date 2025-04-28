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

end
