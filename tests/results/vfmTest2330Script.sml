open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2330Theory;
val () = new_theory "vfmTest2330";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2330") $ get_result_defs "vfmTestDefs2330";
val () = export_theory_no_docs ();
