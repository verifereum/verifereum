open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1075Theory;
val () = new_theory "vfmTest1075";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1075") $ get_result_defs "vfmTestDefs1075";
val () = export_theory_no_docs ();
