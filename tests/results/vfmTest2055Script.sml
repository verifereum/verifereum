open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2055Theory;
val () = new_theory "vfmTest2055";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2055") $ get_result_defs "vfmTestDefs2055";
val () = export_theory_no_docs ();
