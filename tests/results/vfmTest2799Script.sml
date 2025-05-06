open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2799Theory;
val () = new_theory "vfmTest2799";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2799") $ get_result_defs "vfmTestDefs2799";
val () = export_theory_no_docs ();
