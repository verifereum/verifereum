open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2551Theory;
val () = new_theory "vfmTest2551";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2551") $ get_result_defs "vfmTestDefs2551";
val () = export_theory_no_docs ();
