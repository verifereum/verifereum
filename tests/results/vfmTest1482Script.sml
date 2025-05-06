open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1482Theory;
val () = new_theory "vfmTest1482";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1482") $ get_result_defs "vfmTestDefs1482";
val () = export_theory_no_docs ();
