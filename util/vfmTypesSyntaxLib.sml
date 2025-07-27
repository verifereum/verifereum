structure vfmTypesSyntaxLib :> vfmTypesSyntaxLib = struct

  open numSyntax fcpSyntax wordsSyntax optionSyntax listSyntax stringSyntax
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

  val num_from_hex = numSyntax.mk_numeral o Arbnum.fromHexString

  val num_option = mk_option num
  val num_option_from_hex = lift_option num_option num_from_hex

  fun bytes32_from_hex hex = mk_n2w(num_from_hex hex, bytes32_bits_ty)
  fun address_from_hex hex = mk_n2w(num_from_hex hex, address_bits_ty)

  val zero_bytes32 = mk_n2w(numSyntax.zero_tm, bytes32_bits_ty)

end
