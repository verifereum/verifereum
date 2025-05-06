open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2433Theory;
val () = new_theory "vfmTest2433";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2433") $ get_result_defs "vfmTestDefs2433";
val () = export_theory_no_docs ();
