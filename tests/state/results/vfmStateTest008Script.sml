open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs008Theory;
val () = new_theory "vfmStateTest008";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs008";
val () = export_theory_no_docs ();
