open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2382Theory;
val () = new_theory "vfmTest2382";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2382") $ get_result_defs "vfmTestDefs2382";
val () = export_theory_no_docs ();
