open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2921Theory;
val () = new_theory "vfmTest2921";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2921") $ get_result_defs "vfmTestDefs2921";
val () = export_theory_no_docs ();
