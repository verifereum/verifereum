open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1010Theory;
val () = new_theory "vfmTest1010";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1010") $ get_result_defs "vfmTestDefs1010";
val () = export_theory_no_docs ();
