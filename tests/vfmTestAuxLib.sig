signature vfmTestAuxLib = sig

  val ss : (substring -> substring) -> string -> string
  val trimr : int -> string -> string
  val triml : int -> string -> string
  val trim2 : string -> string
  val padl : int -> char -> string -> string
  val string_less : string -> string -> bool

  val export_theory_no_docs: unit -> unit

  val time_limit : Time.time

  val fixtures_version : string
  val fork_name : string
  val chain_id : int

end
