open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2120Theory;
val () = new_theory "vfmTest2120";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2120") $ get_result_defs "vfmTestDefs2120";
val () = export_theory_no_docs ();
