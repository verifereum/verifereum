structure vfmUncheckedFixtureLib :> vfmUncheckedFixtureLib = struct
  structure Fixture = struct open vfmTestDefLib end
  structure ML = struct open vfmUncheckedML end

  val nil_cv = ML.Num Arbnum.zero
  val some_tag = ML.Num Arbnum.one

  fun list_cv encode xs =
    List.foldr (fn (x, rest) => ML.Pair (encode x, rest)) nil_cv xs

  fun option_cv encode NONE = nil_cv
    | option_cv encode (SOME x) = ML.Pair (some_tag, encode x)

  fun num hex = ML.Num (Arbnum.fromHexString hex)

  val address_modulus = Arbnum.pow (Arbnum.two, Arbnum.fromInt 160)
  val bytes32_modulus = Arbnum.pow (Arbnum.two, Arbnum.fromInt 256)

  fun word modulus hex = ML.Num (Arbnum.mod (Arbnum.fromHexString hex, modulus))
  val address = word address_modulus
  val bytes32 = word bytes32_modulus

  fun string_cv str = let
    fun loop i acc =
      if i < 0 then acc
      else loop (i - 1)
        (ML.Pair (ML.Num (Arbnum.fromInt (Char.ord (String.sub (str, i)))), acc))
  in
    loop (String.size str - 1) nil_cv
  end

  (* Match keccak.hex_to_rev_bytes, including its final single hex digit. *)
  fun unhex c =
    if #"0" <= c andalso c <= #"9" then Char.ord c - Char.ord #"0"
    else if #"a" <= c andalso c <= #"f" then Char.ord c - Char.ord #"a" + 10
    else if #"A" <= c andalso c <= #"F" then Char.ord c - Char.ord #"A" + 10
    else 0

  val byte_values = Vector.tabulate (256, ML.Num o Arbnum.fromInt)

  fun hex_start str = if String.isPrefix "0x" str then 2 else 0

  (* Walk backwards to construct the CV list without an intermediate byte list
     or a copy of the hexadecimal substring.  Bounds count hex characters. *)
  fun bytes_range str start size = let
    val paired_size = size - size mod 2
    val suffix =
      if size mod 2 = 0 then nil_cv
      else ML.Pair (Vector.sub (byte_values,
                      unhex (String.sub (str, start + paired_size))), nil_cv)
    fun loop offset acc =
      if offset < start then acc
      else let
        val byte = 16 * unhex (String.sub (str, offset)) +
                   unhex (String.sub (str, offset + 1))
      in
        loop (offset - 2) (ML.Pair (Vector.sub (byte_values, byte), acc))
      end
  in
    loop (start + paired_size - 2) suffix
  end

  fun bytes str = let
    val start = hex_start str
  in
    bytes_range str start (String.size str - start)
  end

  (* These thresholds and chunk boundaries deliberately match byteStringCacheLib.
     Chunking is semantically visible in the run_test RLP arguments. *)
  val regular_hex_chunk_size = 2 * 64 * 1024
  val shared_hex_chunk_size = 2 * 8 * 1024
  val large_hex_threshold = 2 * 1024 * 1024
  val flat_bytes_chunk_threshold = 2 * 64 * 1024

  fun byte_chunks str = let
    val start = hex_start str
    val size = String.size str - start
    val chunk_size = if size > large_hex_threshold
                     then shared_hex_chunk_size else regular_hex_chunk_size
    val () = if size mod 2 = 0 then ()
             else raise Fail "cached_byte_chunks_from_hex: partial-byte chunk"
    fun loop remaining acc =
      if remaining = 0 then acc
      else let
        val offset = ((remaining - 1) div chunk_size) * chunk_size
        val chunk = bytes_range str (start + offset) (remaining - offset)
      in
        loop offset (ML.Pair (chunk, acc))
      end
  in
    loop size nil_cv
  end

  fun flat_bytes str = let
    val size = String.size str - hex_start str
    val () = if size <= flat_bytes_chunk_threshold orelse size mod 2 = 0 then ()
             else raise Fail "cached_byte_chunks_from_hex: partial-byte chunk"
  in
    bytes str
  end

  (* Right folds preserve the certified loader's first-entry-wins update order. *)
  fun storage (slots : Fixture.storage) =
    List.foldr (fn ({key, value}, rest) =>
      ML.update_storage (bytes32 key) (bytes32 value) rest) ML.empty_storage slots

  fun account ({balance, code, nonce, storage = slots} : Fixture.account) =
    ML.account {balance = num balance, nonce = num nonce,
                code = bytes code, storage = storage slots}

  fun accounts (state : Fixture.state) =
    List.foldr (fn ((key, value), rest) =>
      ML.update_account (address key) (account value) rest) ML.empty_accounts state

  fun access_list_entry ({address = key, storageKeys} : Fixture.access_list_entry) =
    ML.access_list_entry {account = address key, keys = list_cv bytes32 storageKeys}

  fun authorization ({chainId, address = delegate, nonce, signer, s}
                     : Fixture.authorization_entry) =
    ML.authorization {authority = address signer, delegate = address delegate,
                      authChainId = num chainId, authNonce = num nonce, authS = num s}

  fun optional_list encode xs = list_cv encode (Option.getOpt (xs, []))

  (* Natural subtraction saturates at zero; Arbnum subtraction need not do so. *)
  fun gas_price base_fee (tx : Fixture.transaction) =
    case #gasPrice tx of
      SOME hex => num hex
    | NONE => let
        val max_fee = Arbnum.fromHexString (Option.valOf (#maxFeePerGas tx))
        val priority_fee = Arbnum.fromHexString
          (Option.valOf (#maxPriorityFeePerGas tx))
        val available = if Arbnum.< (max_fee, base_fee) then Arbnum.zero
                        else Arbnum.- (max_fee, base_fee)
      in
        ML.Num (Arbnum.+ (base_fee, Arbnum.min (priority_fee, available)))
      end

  fun transaction base_fee (tx : Fixture.transaction) =
    ML.transaction {
      to = if #to tx = "" then nil_cv else option_cv address (SOME (#to tx)),
      from = address (#sender tx),
      data = flat_bytes (#data tx),
      nonce = num (#nonce tx),
      value = num (#value tx),
      gasLimit = num (#gasLimit tx),
      gasPrice = gas_price base_fee tx,
      accessList = optional_list access_list_entry (#accessList tx),
      blobVersionedHashes = optional_list bytes32 (#blobVersionedHashes tx),
      maxFeePerGas = option_cv num (#maxFeePerGas tx),
      maxFeePerBlobGas = option_cv num (#maxFeePerBlobGas tx),
      authorizationList = optional_list authorization (#authorizationList tx)
    }

  fun withdrawal ({index, validatorIndex, address = key, amount} : Fixture.withdrawal) =
    ML.withdrawal {withdrawalIndex = num index, validatorIndex = num validatorIndex,
                   withdrawalAddress = address key, withdrawalAmount = num amount}

  (* rlp is the block's RLP as hex; an invalid block's rlp_decoded may lack
     its own copy *)
  fun block rlp (value : Fixture.block) = let
    val header = #blockHeader value
    val base_fee = Arbnum.fromHexString (#baseFeePerGas header)
  in
    ML.block {
      baseFeePerGas = ML.Num base_fee,
      excessBlobGas = num (#excessBlobGas header),
      gasUsed = num (#gasUsed header),
      blobGasUsed = num (#blobGasUsed header),
      number = num (#number header),
      timeStamp = num (#timestamp header),
      coinBase = address (#coinbase header),
      gasLimit = num (#gasLimit header),
      prevRandao = bytes32 (#mixHash header),
      hash = bytes32 (#hash header),
      rlpSize = ML.Num (Arbnum.fromInt ((String.size rlp - hex_start rlp) div 2)),
      parentBeaconBlockRoot = bytes32 (#parentBeaconBlockRoot header),
      requestsHash = bytes32 (#requestsHash header),
      blockAccessListHash = bytes32 (#blockAccessListHash header),
      slotNumber = num (#slotNumber header),
      stateRoot = bytes32 (#stateRoot header),
      withdrawalsRoot = bytes32 (#withdrawalsRoot header),
      transactions = list_cv (transaction base_fee) (#transactions value),
      withdrawals = list_cv withdrawal (#withdrawals value)
    }
  end

  fun test_block (Fixture.Block value) =
        ML.valid_block (block (#rlp value) value) (byte_chunks (#rlp value))
    | test_block (Fixture.Invalid {expectException, rlp, rlp_decoded}) =
        ML.invalid_block (string_cv expectException) (byte_chunks rlp)
          (option_cv (block rlp) rlp_decoded)

  fun run (test : Fixture.test) () = let
    val header = #genesisBlockHeader test
    val genesis : Fixture.block = {
      rlp = #genesisRLP test, blockHeader = header, blocknumber = #number header,
      transactions = [], uncleHeaders = [], withdrawals = [],
      blockAccessList = NONE
    }
  in
    ML.result_string
      (ML.run_test (accounts (#pre test)) (byte_chunks (#genesisRLP test))
        (block (#genesisRLP test) genesis) (list_cv test_block (#blocks test))
        (bytes32 (#lastblockhash test)) (accounts (#post test)))
  end

  (* Invalid blocks can claim any gasUsed, so each block counts at most its
     gasLimit; an invalid block without rlp_decoded counts nothing. *)
  fun header_gas ({gasUsed, gasLimit, ...} : Fixture.block_header) =
    Arbnum.min (Arbnum.fromHexString gasUsed, Arbnum.fromHexString gasLimit)

  fun block_gas (Fixture.Block value) = header_gas (#blockHeader value)
    | block_gas (Fixture.Invalid {rlp_decoded, ...}) =
        case rlp_decoded of
          SOME value => header_gas (#blockHeader value)
        | NONE => Arbnum.zero

  fun json_path_to_tests path =
    List.map (fn test => {
        name = #name test,
        gas = List.foldl (fn (b, total) => Arbnum.+ (block_gas b, total))
                Arbnum.zero (#blocks test),
        evaluate = run test
      }) (Fixture.json_path_to_tests path)
end
