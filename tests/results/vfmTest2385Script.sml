open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2385Theory;
val () = new_theory "vfmTest2385";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2385") $ get_result_defs "vfmTestDefs2385";
val () = export_theory_no_docs ();
