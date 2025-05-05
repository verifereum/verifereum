open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs042Theory;
val () = new_theory "vfmStateTest042";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs042") $ get_result_defs "vfmStateTestDefs042";
val () = export_theory_no_docs ();
