open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2056Theory;
val () = new_theory "vfmTest2056";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2056") $ get_result_defs "vfmTestDefs2056";
val () = export_theory_no_docs ();
