open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2427Theory;
val () = new_theory "vfmTest2427";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2427") $ get_result_defs "vfmTestDefs2427";
val () = export_theory_no_docs ();
