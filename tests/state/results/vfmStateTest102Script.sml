open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs102Theory;
val () = new_theory "vfmStateTest102";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs102") $ get_result_defs "vfmStateTestDefs102";
val () = export_theory_no_docs ();
