open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1962Theory;
val () = new_theory "vfmTest1962";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1962") $ get_result_defs "vfmTestDefs1962";
val () = export_theory_no_docs ();
