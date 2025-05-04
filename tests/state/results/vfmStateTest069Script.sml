open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs069Theory;
val () = new_theory "vfmStateTest069";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs069";
val () = export_theory_no_docs ();
