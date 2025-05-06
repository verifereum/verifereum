open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2088Theory;
val () = new_theory "vfmTest2088";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2088") $ get_result_defs "vfmTestDefs2088";
val () = export_theory_no_docs ();
