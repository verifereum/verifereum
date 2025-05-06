open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2255Theory;
val () = new_theory "vfmTest2255";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2255") $ get_result_defs "vfmTestDefs2255";
val () = export_theory_no_docs ();
