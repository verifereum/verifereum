open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2188Theory;
val () = new_theory "vfmTest2188";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2188") $ get_result_defs "vfmTestDefs2188";
val () = export_theory_no_docs ();
