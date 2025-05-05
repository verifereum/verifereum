open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs003Theory;
val () = new_theory "vfmStateTest003";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs003") $ get_result_defs "vfmStateTestDefs003";
val () = export_theory_no_docs ();
