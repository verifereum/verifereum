open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1523Theory;
val () = new_theory "vfmTest1523";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1523") $ get_result_defs "vfmTestDefs1523";
val () = export_theory_no_docs ();
