signature vfmUncheckedFixtureLib = sig
  (* Parsing is shared with the certified loader.  Each closure performs all
     native fixture encoding and execution, so both are covered by its timeout. *)
  val json_path_to_tests : string -> (string * (unit -> string)) list
end
