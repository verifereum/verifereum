open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs154Theory;
val () = new_theory "vfmStateTest154";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs154";
val () = export_theory_no_docs ();
