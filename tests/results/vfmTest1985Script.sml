open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1985Theory;
val () = new_theory "vfmTest1985";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1985") $ get_result_defs "vfmTestDefs1985";
val () = export_theory_no_docs ();
