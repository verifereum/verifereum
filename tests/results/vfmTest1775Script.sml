open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1775Theory;
val () = new_theory "vfmTest1775";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1775") $ get_result_defs "vfmTestDefs1775";
val () = export_theory_no_docs ();
