open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2340Theory;
val () = new_theory "vfmTest2340";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2340") $ get_result_defs "vfmTestDefs2340";
val () = export_theory_no_docs ();
