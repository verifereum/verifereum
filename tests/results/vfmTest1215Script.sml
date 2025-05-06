open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1215Theory;
val () = new_theory "vfmTest1215";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1215") $ get_result_defs "vfmTestDefs1215";
val () = export_theory_no_docs ();
