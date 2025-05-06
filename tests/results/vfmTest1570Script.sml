open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1570Theory;
val () = new_theory "vfmTest1570";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1570") $ get_result_defs "vfmTestDefs1570";
val () = export_theory_no_docs ();
