open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1351Theory;
val () = new_theory "vfmTest1351";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1351") $ get_result_defs "vfmTestDefs1351";
val () = export_theory_no_docs ();
