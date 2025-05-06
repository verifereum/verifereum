open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2212Theory;
val () = new_theory "vfmTest2212";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2212") $ get_result_defs "vfmTestDefs2212";
val () = export_theory_no_docs ();
