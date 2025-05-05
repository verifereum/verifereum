open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs133Theory;
val () = new_theory "vfmStateTest133";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs133") $ get_result_defs "vfmStateTestDefs133";
val () = export_theory_no_docs ();
