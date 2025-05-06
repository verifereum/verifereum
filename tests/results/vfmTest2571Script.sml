open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2571Theory;
val () = new_theory "vfmTest2571";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2571") $ get_result_defs "vfmTestDefs2571";
val () = export_theory_no_docs ();
