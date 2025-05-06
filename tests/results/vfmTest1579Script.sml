open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1579Theory;
val () = new_theory "vfmTest1579";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1579") $ get_result_defs "vfmTestDefs1579";
val () = export_theory_no_docs ();
