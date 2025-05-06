open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2856Theory;
val () = new_theory "vfmTest2856";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2856") $ get_result_defs "vfmTestDefs2856";
val () = export_theory_no_docs ();
