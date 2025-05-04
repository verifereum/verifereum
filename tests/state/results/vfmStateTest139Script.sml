open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs139Theory;
val () = new_theory "vfmStateTest139";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs139";
val () = export_theory_no_docs ();
