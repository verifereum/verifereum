open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2514Theory;
val () = new_theory "vfmTest2514";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2514") $ get_result_defs "vfmTestDefs2514";
val () = export_theory_no_docs ();
