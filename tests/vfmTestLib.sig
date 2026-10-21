signature vfmTestLib = sig

  val ensure_fixtures : unit -> unit
  val get_all_test_json_paths : unit -> string list
  (* index strings, as in test theory names, of the given fixture json paths *)
  val test_indices : string list -> string list
  val system_or_fail : string -> string -> unit
  val collect_script_files : string -> string list
  val remove_nsv_files : string -> unit
  val generate_test_defs_scripts : unit -> unit
  val generate_test_results_scripts : unit -> unit
  val write_test_results_table : unit -> unit

end
