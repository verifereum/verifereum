open HolKernel vfmTestAuxLib vfmTestResultLib vfmStateTestDefs088Theory;
val () = new_theory "vfmStateTest088";
val () = List.app (ignore o save_result_thm default_limit "vfmStateTestDefs088") $ get_result_defs "vfmStateTestDefs088";
val () = export_theory_no_docs ();
