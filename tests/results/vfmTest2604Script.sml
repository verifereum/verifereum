open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2604Theory;
val () = new_theory "vfmTest2604";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2604") $ get_result_defs "vfmTestDefs2604";
val () = export_theory_no_docs ();
