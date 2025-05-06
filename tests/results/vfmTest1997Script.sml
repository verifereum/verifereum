open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1997Theory;
val () = new_theory "vfmTest1997";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1997") $ get_result_defs "vfmTestDefs1997";
val () = export_theory_no_docs ();
