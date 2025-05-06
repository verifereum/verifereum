open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1983Theory;
val () = new_theory "vfmTest1983";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1983") $ get_result_defs "vfmTestDefs1983";
val () = export_theory_no_docs ();
