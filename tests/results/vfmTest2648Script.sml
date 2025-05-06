open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2648Theory;
val () = new_theory "vfmTest2648";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2648") $ get_result_defs "vfmTestDefs2648";
val () = export_theory_no_docs ();
