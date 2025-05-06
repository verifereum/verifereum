open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1452Theory;
val () = new_theory "vfmTest1452";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1452") $ get_result_defs "vfmTestDefs1452";
val () = export_theory_no_docs ();
