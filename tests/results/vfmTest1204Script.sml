open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1204Theory;
val () = new_theory "vfmTest1204";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1204") $ get_result_defs "vfmTestDefs1204";
val () = export_theory_no_docs ();
