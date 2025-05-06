open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1632Theory;
val () = new_theory "vfmTest1632";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1632") $ get_result_defs "vfmTestDefs1632";
val () = export_theory_no_docs ();
