open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1655Theory;
val () = new_theory "vfmTest1655";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1655") $ get_result_defs "vfmTestDefs1655";
val () = export_theory_no_docs ();
