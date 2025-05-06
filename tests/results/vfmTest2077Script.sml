open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2077Theory;
val () = new_theory "vfmTest2077";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2077") $ get_result_defs "vfmTestDefs2077";
val () = export_theory_no_docs ();
