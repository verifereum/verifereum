open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs156Theory;
val () = new_theory "vfmStateTest156";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs156") $ get_result_defs "vfmStateTestDefs156";
val () = export_theory_no_docs ();
