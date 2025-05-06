open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1650Theory;
val () = new_theory "vfmTest1650";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1650") $ get_result_defs "vfmTestDefs1650";
val () = export_theory_no_docs ();
