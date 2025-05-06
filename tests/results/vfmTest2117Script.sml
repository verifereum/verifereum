open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2117Theory;
val () = new_theory "vfmTest2117";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2117") $ get_result_defs "vfmTestDefs2117";
val () = export_theory_no_docs ();
