open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2026Theory;
val () = new_theory "vfmTest2026";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2026") $ get_result_defs "vfmTestDefs2026";
val () = export_theory_no_docs ();
