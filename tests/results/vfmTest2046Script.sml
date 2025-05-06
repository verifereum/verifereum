open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2046Theory;
val () = new_theory "vfmTest2046";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2046") $ get_result_defs "vfmTestDefs2046";
val () = export_theory_no_docs ();
