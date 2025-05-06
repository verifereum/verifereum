open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2704Theory;
val () = new_theory "vfmTest2704";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2704") $ get_result_defs "vfmTestDefs2704";
val () = export_theory_no_docs ();
