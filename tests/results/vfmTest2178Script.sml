open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2178Theory;
val () = new_theory "vfmTest2178";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2178") $ get_result_defs "vfmTestDefs2178";
val () = export_theory_no_docs ();
