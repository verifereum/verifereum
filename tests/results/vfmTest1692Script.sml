open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1692Theory;
val () = new_theory "vfmTest1692";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1692") $ get_result_defs "vfmTestDefs1692";
val () = export_theory_no_docs ();
