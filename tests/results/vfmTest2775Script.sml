open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2775Theory;
val () = new_theory "vfmTest2775";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2775") $ get_result_defs "vfmTestDefs2775";
val () = export_theory_no_docs ();
