open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs143Theory;
val () = new_theory "vfmStateTest143";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs143") $ get_result_defs "vfmStateTestDefs143";
val () = export_theory_no_docs ();
