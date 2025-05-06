open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1637Theory;
val () = new_theory "vfmTest1637";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1637") $ get_result_defs "vfmTestDefs1637";
val () = export_theory_no_docs ();
