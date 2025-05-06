open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1465Theory;
val () = new_theory "vfmTest1465";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1465") $ get_result_defs "vfmTestDefs1465";
val () = export_theory_no_docs ();
