signature vfmTestAuxLib = sig

  val ss : (substring -> substring) -> string -> string
  val trimr : int -> string -> string
  val triml : int -> string -> string
  val trim2 : string -> string
  val padl : int -> char -> string -> string
  val string_less : string -> string -> bool

  val holbuild_extra_deps : string list -> unit
  val holbuild_extra_outputs : string list -> unit

  val test_root : unit -> string
  val test_path : string -> string
  val fixtures_path : string -> string
  val defs_path : string -> string
  val results_path : string -> string

  val time_limit : Time.time

  val fixtures_version : string
  val fork_name : string
  val chain_id : int

end
