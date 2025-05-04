open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs059Theory;
val () = new_theory "vfmStateTest059";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs059";
val () = export_theory_no_docs ();
