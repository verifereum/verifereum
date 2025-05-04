open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs080Theory;
val () = new_theory "vfmStateTest080";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs080";
val () = export_theory_no_docs ();
