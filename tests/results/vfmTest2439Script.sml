open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2439Theory;
val () = new_theory "vfmTest2439";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2439") $ get_result_defs "vfmTestDefs2439";
val () = export_theory_no_docs ();
