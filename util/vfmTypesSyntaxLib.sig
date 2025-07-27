signature vfmTypesSyntaxLib = sig

  val address_bits_ty : hol_type
  val bytes32_bits_ty : hol_type
  val address_ty      : hol_type
  val bytes32_ty      : hol_type

  val byte_ty         : hol_type
  val bytes_ty        : hol_type

  val hex_to_rev_bytes_tm : term
  val mk_hex_to_rev_bytes_tm_from_string : string -> term

end
