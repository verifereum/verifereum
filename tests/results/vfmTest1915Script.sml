open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1915Theory;
val () = new_theory "vfmTest1915";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1915") $ get_result_defs "vfmTestDefs1915";
val () = export_theory_no_docs ();
