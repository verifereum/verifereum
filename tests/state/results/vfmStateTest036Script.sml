open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs036Theory;
val () = new_theory "vfmStateTest036";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs036") $ get_result_defs "vfmStateTestDefs036";
val () = export_theory_no_docs ();
