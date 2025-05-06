open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2554Theory;
val () = new_theory "vfmTest2554";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2554") $ get_result_defs "vfmTestDefs2554";
val () = export_theory_no_docs ();
