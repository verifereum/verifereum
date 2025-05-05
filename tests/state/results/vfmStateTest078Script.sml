open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs078Theory;
val () = new_theory "vfmStateTest078";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs078") $ get_result_defs "vfmStateTestDefs078";
val () = export_theory_no_docs ();
