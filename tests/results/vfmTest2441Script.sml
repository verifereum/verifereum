open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2441Theory;
val () = new_theory "vfmTest2441";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2441") $ get_result_defs "vfmTestDefs2441";
val () = export_theory_no_docs ();
