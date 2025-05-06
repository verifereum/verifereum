open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1331Theory;
val () = new_theory "vfmTest1331";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1331") $ get_result_defs "vfmTestDefs1331";
val () = export_theory_no_docs ();
