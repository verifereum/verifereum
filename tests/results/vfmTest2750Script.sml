open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2750Theory;
val () = new_theory "vfmTest2750";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2750") $ get_result_defs "vfmTestDefs2750";
val () = export_theory_no_docs ();
