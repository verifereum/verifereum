open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2865Theory;
val () = new_theory "vfmTest2865";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2865") $ get_result_defs "vfmTestDefs2865";
val () = export_theory_no_docs ();
