structure byteStringCacheLib :> byteStringCacheLib = struct

  open HolKernel boolLib cv_transLib vfmTypesSyntax

  val bytestr_cache : (string, term) Redblackmap.dict ref =
    ref $ Redblackmap.mkDict String.compare

  val flat_bytestr_cache : (string, term) Redblackmap.dict ref =
    ref $ Redblackmap.mkDict String.compare

  fun cached_bytes_from_hex str = let
  val hex = if String.isPrefix "0x" str
            then String.extract(str, 2, NONE) else str in
  case Redblackmap.peek(!bytestr_cache, hex)
    of SOME const => const | NONE =>
  let
    val n = Redblackmap.numItems $ !bytestr_cache
    val name = String.concat["bytestr_", Int.toString n]
    val var = mk_var(name, bytes_ty)
    val rhs_tm = mk_hex_to_rev_bytes_tm_from_string hex
    val def = new_definition(name ^ "_def", mk_eq(var, rhs_tm))
    val () = cv_trans_deep_embedding computeLib.EVAL_CONV def
    val const = lhs (concl def)
    val cache = Redblackmap.insert(!bytestr_cache, hex, const)
    val () = bytestr_cache := cache
  in const end
  end

  (* Keep each generated HOL string and deep embedding to a moderate size.
     The unit is hexadecimal characters, so this represents 8 KiB of bytes. *)
  val hex_chunk_size = 2 * 8 * 1024

  (* Small flat values do not benefit enough from an aggregate definition to
     justify its overhead. *)
  val flat_bytes_chunk_threshold = 2 * 64 * 1024

  fun cached_byte_chunks_from_hex str = let
    val hex = if String.isPrefix "0x" str
              then String.extract(str, 2, NONE) else str
    val size = String.size hex
    fun split offset acc =
      if offset = size then List.rev acc
      else let
        val remaining = size - offset
        val chunk_size = Int.min(hex_chunk_size, remaining)
        val chunk = String.substring(hex, offset, chunk_size)
      in
        split (offset + chunk_size) (chunk :: acc)
      end
    val chunk_strings = split 0 []
    val () =
      if List.all (fn chunk => String.size chunk mod 2 = 0) chunk_strings
      then ()
      else raise Fail "cached_byte_chunks_from_hex: partial-byte chunk"
    val () =
      if String.concat chunk_strings = hex then ()
      else raise Fail "cached_byte_chunks_from_hex: reconstruction failed"
    val chunks = List.map cached_bytes_from_hex chunk_strings
  in
    listSyntax.mk_list(chunks, bytes_ty)
  end

  (* Preserve the ordinary flat byte-list type while keeping large source
     values compositional in their definitions and cv translations. *)
  fun cached_flat_bytes_from_hex str = let
    val hex = if String.isPrefix "0x" str
              then String.extract(str, 2, NONE) else str
  in
    if String.size hex <= flat_bytes_chunk_threshold
    then cached_bytes_from_hex hex
    else
      case Redblackmap.peek(!flat_bytestr_cache, hex) of
        SOME const => const
      | NONE => let
          val n = Redblackmap.numItems $ !flat_bytestr_cache
          val name = "flat_bytestr_" ^ Int.toString n
          val var = mk_var(name, bytes_ty)
          val chunks = cached_byte_chunks_from_hex hex
          val chunks_ty = listSyntax.mk_list_type bytes_ty
          val flat_tm = mk_thy_const{Name="FLAT", Thy="list",
                                     Ty=chunks_ty --> bytes_ty}
          val def = new_definition(name ^ "_def",
                                   mk_eq(var, mk_comb(flat_tm, chunks)))
          val () = cv_trans def
          val const = lhs $ concl def
          val cache = Redblackmap.insert(!flat_bytestr_cache, hex, const)
          val () = flat_bytestr_cache := cache
        in
          const
        end
  end

end
