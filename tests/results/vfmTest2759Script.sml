open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2759Theory;
val () = new_theory "vfmTest2759";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2759") $ get_result_defs "vfmTestDefs2759";
val () = export_theory_no_docs ();
