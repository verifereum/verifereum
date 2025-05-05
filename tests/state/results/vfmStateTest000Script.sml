open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs000Theory;
val () = new_theory "vfmStateTest000";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs000") $ get_result_defs "vfmStateTestDefs000";
val () = export_theory_no_docs ();
