open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2041Theory;
val () = new_theory "vfmTest2041";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2041") $ get_result_defs "vfmTestDefs2041";
val () = export_theory_no_docs ();
