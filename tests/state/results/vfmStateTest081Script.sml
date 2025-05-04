open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs081Theory;
val () = new_theory "vfmStateTest081";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs081";
val () = export_theory_no_docs ();
