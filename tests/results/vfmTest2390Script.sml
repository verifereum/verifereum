open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2390Theory;
val () = new_theory "vfmTest2390";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2390") $ get_result_defs "vfmTestDefs2390";
val () = export_theory_no_docs ();
