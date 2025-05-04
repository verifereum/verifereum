open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs054Theory;
val () = new_theory "vfmStateTest054";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs054";
val () = export_theory_no_docs ();
