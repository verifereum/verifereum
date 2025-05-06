open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1448Theory;
val () = new_theory "vfmTest1448";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1448") $ get_result_defs "vfmTestDefs1448";
val () = export_theory_no_docs ();
