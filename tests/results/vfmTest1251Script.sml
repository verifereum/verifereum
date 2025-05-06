open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1251Theory;
val () = new_theory "vfmTest1251";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1251") $ get_result_defs "vfmTestDefs1251";
val () = export_theory_no_docs ();
