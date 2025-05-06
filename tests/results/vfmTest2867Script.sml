open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2867Theory;
val () = new_theory "vfmTest2867";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2867") $ get_result_defs "vfmTestDefs2867";
val () = export_theory_no_docs ();
