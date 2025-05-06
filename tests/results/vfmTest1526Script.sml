open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1526Theory;
val () = new_theory "vfmTest1526";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1526") $ get_result_defs "vfmTestDefs1526";
val () = export_theory_no_docs ();
