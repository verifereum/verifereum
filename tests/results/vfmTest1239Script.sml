open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1239Theory;
val () = new_theory "vfmTest1239";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1239") $ get_result_defs "vfmTestDefs1239";
val () = export_theory_no_docs ();
