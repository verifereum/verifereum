open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1598Theory;
val () = new_theory "vfmTest1598";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1598") $ get_result_defs "vfmTestDefs1598";
val () = export_theory_no_docs ();
