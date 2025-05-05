open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs030Theory;
val () = new_theory "vfmStateTest030";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs030") $ get_result_defs "vfmStateTestDefs030";
val () = export_theory_no_docs ();
