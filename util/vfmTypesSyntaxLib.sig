signature vfmTypesSyntaxLib = sig
  include Abbrev

  val hex_to_rev_bytes_tm : term
  val mk_hex_to_rev_bytes_tm_from_string : string -> term

  val address_bits_ty : hol_type
  val bytes32_bits_ty : hol_type
  val address_ty      : hol_type
  val bytes32_ty      : hol_type

  val byte_ty         : hol_type
  val bytes_ty        : hol_type

  val num_from_hex        : string -> term
  val num_option_from_hex : string option -> term
  val bytes32_from_hex    : string -> term
  val address_from_hex    : string -> term

  val zero_bytes32 : term

end
