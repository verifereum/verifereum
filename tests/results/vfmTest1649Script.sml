open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1649Theory;
val () = new_theory "vfmTest1649";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1649") $ get_result_defs "vfmTestDefs1649";
val () = export_theory_no_docs ();
