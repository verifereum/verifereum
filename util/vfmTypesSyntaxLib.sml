structure vfmTypesSyntaxLib :> vfmTypesSyntaxLib = struct

  open fcpSyntax wordsSyntax listSyntax stringSyntax
  open keccakTheory (* TODO: move hex_to_rev_bytes out *)

  val address_bits_ty = mk_int_numeric_type 160
  val bytes32_bits_ty = mk_int_numeric_type 256
  val address_ty = mk_word_type address_bits_ty
  val bytes32_ty = mk_word_type bytes32_bits_ty

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

end
