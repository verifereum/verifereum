structure byteStringCacheLib :> byteStringCacheLib = struct

  open HolKernel boolLib cv_transLib vfmTypesSyntax 

  val bytestr_cache : (string, term) Redblackmap.dict ref =
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

end
