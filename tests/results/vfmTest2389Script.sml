open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2389Theory;
val () = new_theory "vfmTest2389";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2389") $ get_result_defs "vfmTestDefs2389";
val () = export_theory_no_docs ();
