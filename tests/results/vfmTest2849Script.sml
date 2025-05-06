open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2849Theory;
val () = new_theory "vfmTest2849";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2849") $ get_result_defs "vfmTestDefs2849";
val () = export_theory_no_docs ();
