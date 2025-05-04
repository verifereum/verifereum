open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs049Theory;
val () = new_theory "vfmStateTest049";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs049";
val () = export_theory_no_docs ();
