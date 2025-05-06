open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1446Theory;
val () = new_theory "vfmTest1446";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1446") $ get_result_defs "vfmTestDefs1446";
val () = export_theory_no_docs ();
