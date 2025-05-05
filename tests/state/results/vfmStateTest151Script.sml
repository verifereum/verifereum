open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs151Theory;
val () = new_theory "vfmStateTest151";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs151") $ get_result_defs "vfmStateTestDefs151";
val () = export_theory_no_docs ();
