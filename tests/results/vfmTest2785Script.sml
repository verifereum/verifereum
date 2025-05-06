open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2785Theory;
val () = new_theory "vfmTest2785";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2785") $ get_result_defs "vfmTestDefs2785";
val () = export_theory_no_docs ();
