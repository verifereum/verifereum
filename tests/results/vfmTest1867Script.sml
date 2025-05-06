open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1867Theory;
val () = new_theory "vfmTest1867";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1867") $ get_result_defs "vfmTestDefs1867";
val () = export_theory_no_docs ();
