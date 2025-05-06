open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2481Theory;
val () = new_theory "vfmTest2481";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2481") $ get_result_defs "vfmTestDefs2481";
val () = export_theory_no_docs ();
