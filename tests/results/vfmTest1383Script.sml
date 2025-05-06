open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1383Theory;
val () = new_theory "vfmTest1383";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1383") $ get_result_defs "vfmTestDefs1383";
val () = export_theory_no_docs ();
