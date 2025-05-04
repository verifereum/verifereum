open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs164Theory;
val () = new_theory "vfmStateTest164";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs164";
val () = export_theory_no_docs ();
