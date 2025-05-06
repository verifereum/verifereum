open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1333Theory;
val () = new_theory "vfmTest1333";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1333") $ get_result_defs "vfmTestDefs1333";
val () = export_theory_no_docs ();
