open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1592Theory;
val () = new_theory "vfmTest1592";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1592") $ get_result_defs "vfmTestDefs1592";
val () = export_theory_no_docs ();
