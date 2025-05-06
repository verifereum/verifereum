open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2223Theory;
val () = new_theory "vfmTest2223";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2223") $ get_result_defs "vfmTestDefs2223";
val () = export_theory_no_docs ();
