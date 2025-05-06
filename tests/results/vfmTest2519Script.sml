open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2519Theory;
val () = new_theory "vfmTest2519";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2519") $ get_result_defs "vfmTestDefs2519";
val () = export_theory_no_docs ();
