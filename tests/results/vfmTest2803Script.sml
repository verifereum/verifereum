open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2803Theory;
val () = new_theory "vfmTest2803";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2803") $ get_result_defs "vfmTestDefs2803";
val () = export_theory_no_docs ();
