open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1506Theory;
val () = new_theory "vfmTest1506";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1506") $ get_result_defs "vfmTestDefs1506";
val () = export_theory_no_docs ();
