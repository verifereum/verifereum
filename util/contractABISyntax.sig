signature contractABISyntax = sig
  include Abbrev

  val abi_type_ty   : hol_type
  val Bool_tm    : term
  val String_tm  : term
  val Bytes_tm   : term
  val Uint_tm    : term
  val Int_tm     : term
  val Array_tm   : term
  val Tuple_tm   : term
  val Address_tm : term

  val parse_optnum_ss   : Substring.substring -> term
  val parse_abi_type_ss : Substring.substring -> term
  val parse_abi_type : string -> term

end
