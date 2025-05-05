open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs018Theory;
val () = new_theory "vfmStateTest018";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs018") $ get_result_defs "vfmStateTestDefs018";
val () = export_theory_no_docs ();
