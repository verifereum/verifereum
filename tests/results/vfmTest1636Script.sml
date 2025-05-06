open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1636Theory;
val () = new_theory "vfmTest1636";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1636") $ get_result_defs "vfmTestDefs1636";
val () = export_theory_no_docs ();
