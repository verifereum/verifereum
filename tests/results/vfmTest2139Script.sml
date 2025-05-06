open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2139Theory;
val () = new_theory "vfmTest2139";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2139") $ get_result_defs "vfmTestDefs2139";
val () = export_theory_no_docs ();
