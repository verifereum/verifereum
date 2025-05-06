open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2447Theory;
val () = new_theory "vfmTest2447";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2447") $ get_result_defs "vfmTestDefs2447";
val () = export_theory_no_docs ();
