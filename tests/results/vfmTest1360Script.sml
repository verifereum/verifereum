open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1360Theory;
val () = new_theory "vfmTest1360";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1360") $ get_result_defs "vfmTestDefs1360";
val () = export_theory_no_docs ();
