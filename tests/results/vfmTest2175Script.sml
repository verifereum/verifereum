open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2175Theory;
val () = new_theory "vfmTest2175";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2175") $ get_result_defs "vfmTestDefs2175";
val () = export_theory_no_docs ();
