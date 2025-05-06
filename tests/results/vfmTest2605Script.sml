open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2605Theory;
val () = new_theory "vfmTest2605";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2605") $ get_result_defs "vfmTestDefs2605";
val () = export_theory_no_docs ();
