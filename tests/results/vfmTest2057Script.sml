open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2057Theory;
val () = new_theory "vfmTest2057";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2057") $ get_result_defs "vfmTestDefs2057";
val () = export_theory_no_docs ();
