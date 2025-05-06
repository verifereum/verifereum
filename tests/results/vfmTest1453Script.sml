open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1453Theory;
val () = new_theory "vfmTest1453";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1453") $ get_result_defs "vfmTestDefs1453";
val () = export_theory_no_docs ();
