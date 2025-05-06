open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1242Theory;
val () = new_theory "vfmTest1242";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1242") $ get_result_defs "vfmTestDefs1242";
val () = export_theory_no_docs ();
