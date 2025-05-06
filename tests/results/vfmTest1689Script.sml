open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1689Theory;
val () = new_theory "vfmTest1689";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1689") $ get_result_defs "vfmTestDefs1689";
val () = export_theory_no_docs ();
