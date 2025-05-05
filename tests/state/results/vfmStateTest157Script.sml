open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs157Theory;
val () = new_theory "vfmStateTest157";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs157") $ get_result_defs "vfmStateTestDefs157";
val () = export_theory_no_docs ();
