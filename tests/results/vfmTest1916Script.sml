open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1916Theory;
val () = new_theory "vfmTest1916";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1916") $ get_result_defs "vfmTestDefs1916";
val () = export_theory_no_docs ();
