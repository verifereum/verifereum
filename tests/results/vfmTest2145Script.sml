open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2145Theory;
val () = new_theory "vfmTest2145";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2145") $ get_result_defs "vfmTestDefs2145";
val () = export_theory_no_docs ();
