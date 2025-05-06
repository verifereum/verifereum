open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1525Theory;
val () = new_theory "vfmTest1525";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1525") $ get_result_defs "vfmTestDefs1525";
val () = export_theory_no_docs ();
