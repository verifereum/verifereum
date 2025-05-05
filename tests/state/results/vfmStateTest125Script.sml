open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs125Theory;
val () = new_theory "vfmStateTest125";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs125") $ get_result_defs "vfmStateTestDefs125";
val () = export_theory_no_docs ();
