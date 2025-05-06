open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2597Theory;
val () = new_theory "vfmTest2597";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2597") $ get_result_defs "vfmTestDefs2597";
val () = export_theory_no_docs ();
