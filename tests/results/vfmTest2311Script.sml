open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2311Theory;
val () = new_theory "vfmTest2311";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2311") $ get_result_defs "vfmTestDefs2311";
val () = export_theory_no_docs ();
