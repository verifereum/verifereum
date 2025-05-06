open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1088Theory;
val () = new_theory "vfmTest1088";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1088") $ get_result_defs "vfmTestDefs1088";
val () = export_theory_no_docs ();
