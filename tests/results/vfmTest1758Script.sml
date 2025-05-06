open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1758Theory;
val () = new_theory "vfmTest1758";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1758") $ get_result_defs "vfmTestDefs1758";
val () = export_theory_no_docs ();
