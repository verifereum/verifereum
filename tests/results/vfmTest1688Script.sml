open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1688Theory;
val () = new_theory "vfmTest1688";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1688") $ get_result_defs "vfmTestDefs1688";
val () = export_theory_no_docs ();
