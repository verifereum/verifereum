open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs064Theory;
val () = new_theory "vfmStateTest064";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs064";
val () = export_theory_no_docs ();
