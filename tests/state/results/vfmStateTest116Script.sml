open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs116Theory;
val () = new_theory "vfmStateTest116";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs116") $ get_result_defs "vfmStateTestDefs116";
val () = export_theory_no_docs ();
