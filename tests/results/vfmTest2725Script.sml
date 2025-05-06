open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2725Theory;
val () = new_theory "vfmTest2725";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2725") $ get_result_defs "vfmTestDefs2725";
val () = export_theory_no_docs ();
