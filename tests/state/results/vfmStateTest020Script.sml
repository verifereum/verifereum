open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs020Theory;
val () = new_theory "vfmStateTest020";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs020") $ get_result_defs "vfmStateTestDefs020";
val () = export_theory_no_docs ();
