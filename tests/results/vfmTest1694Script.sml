open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1694Theory;
val () = new_theory "vfmTest1694";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1694") $ get_result_defs "vfmTestDefs1694";
val () = export_theory_no_docs ();
