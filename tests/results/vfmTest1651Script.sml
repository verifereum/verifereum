open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1651Theory;
val () = new_theory "vfmTest1651";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1651") $ get_result_defs "vfmTestDefs1651";
val () = export_theory_no_docs ();
