open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2058Theory;
val () = new_theory "vfmTest2058";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2058") $ get_result_defs "vfmTestDefs2058";
val () = export_theory_no_docs ();
