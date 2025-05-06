open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1273Theory;
val () = new_theory "vfmTest1273";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1273") $ get_result_defs "vfmTestDefs1273";
val () = export_theory_no_docs ();
