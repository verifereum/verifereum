open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2252Theory;
val () = new_theory "vfmTest2252";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2252") $ get_result_defs "vfmTestDefs2252";
val () = export_theory_no_docs ();
