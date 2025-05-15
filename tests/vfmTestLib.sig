signature vfmTestLib = sig

  val ensure_fixtures : unit -> unit
  val system_or_fail : string -> string -> unit
  val generate_test_defs_scripts : unit -> unit
  val generate_test_results_scripts : unit -> unit
  val write_test_results_table : unit -> unit

end
