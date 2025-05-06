open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1068Theory;
val () = new_theory "vfmTest1068";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1068") $ get_result_defs "vfmTestDefs1068";
val () = export_theory_no_docs ();
