open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2528Theory;
val () = new_theory "vfmTest2528";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2528") $ get_result_defs "vfmTestDefs2528";
val () = export_theory_no_docs ();
