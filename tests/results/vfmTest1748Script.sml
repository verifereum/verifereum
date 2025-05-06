open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1748Theory;
val () = new_theory "vfmTest1748";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1748") $ get_result_defs "vfmTestDefs1748";
val () = export_theory_no_docs ();
