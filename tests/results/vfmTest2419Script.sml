open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2419Theory;
val () = new_theory "vfmTest2419";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2419") $ get_result_defs "vfmTestDefs2419";
val () = export_theory_no_docs ();
