open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1560Theory;
val () = new_theory "vfmTest1560";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1560") $ get_result_defs "vfmTestDefs1560";
val () = export_theory_no_docs ();
