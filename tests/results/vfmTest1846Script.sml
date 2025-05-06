open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1846Theory;
val () = new_theory "vfmTest1846";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1846") $ get_result_defs "vfmTestDefs1846";
val () = export_theory_no_docs ();
