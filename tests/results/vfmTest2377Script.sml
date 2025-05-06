open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2377Theory;
val () = new_theory "vfmTest2377";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2377") $ get_result_defs "vfmTestDefs2377";
val () = export_theory_no_docs ();
