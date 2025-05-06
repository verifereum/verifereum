open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1012Theory;
val () = new_theory "vfmTest1012";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1012") $ get_result_defs "vfmTestDefs1012";
val () = export_theory_no_docs ();
