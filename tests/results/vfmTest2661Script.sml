open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2661Theory;
val () = new_theory "vfmTest2661";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2661") $ get_result_defs "vfmTestDefs2661";
val () = export_theory_no_docs ();
