open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs166Theory;
val () = new_theory "vfmStateTest166";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs166") $ get_result_defs "vfmStateTestDefs166";
val () = export_theory_no_docs ();
