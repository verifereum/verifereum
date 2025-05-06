open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1036Theory;
val () = new_theory "vfmTest1036";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1036") $ get_result_defs "vfmTestDefs1036";
val () = export_theory_no_docs ();
