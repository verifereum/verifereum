open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2546Theory;
val () = new_theory "vfmTest2546";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2546") $ get_result_defs "vfmTestDefs2546";
val () = export_theory_no_docs ();
