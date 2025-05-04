open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs144Theory;
val () = new_theory "vfmStateTest144";
val () = List.app (ignore o save_result_thm default_limit) $ get_result_defs "vfmStateTestDefs144";
val () = export_theory_no_docs ();
