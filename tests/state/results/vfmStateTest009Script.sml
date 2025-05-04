open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs009Theory;
val () = new_theory "vfmStateTest009";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs009";
val () = export_theory_no_docs ();
