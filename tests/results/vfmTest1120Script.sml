open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1120Theory;
val () = new_theory "vfmTest1120";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1120") $ get_result_defs "vfmTestDefs1120";
val () = export_theory_no_docs ();
