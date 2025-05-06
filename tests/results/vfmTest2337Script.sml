open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2337Theory;
val () = new_theory "vfmTest2337";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2337") $ get_result_defs "vfmTestDefs2337";
val () = export_theory_no_docs ();
