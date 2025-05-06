open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1741Theory;
val () = new_theory "vfmTest1741";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1741") $ get_result_defs "vfmTestDefs1741";
val () = export_theory_no_docs ();
