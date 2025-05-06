open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2273Theory;
val () = new_theory "vfmTest2273";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2273") $ get_result_defs "vfmTestDefs2273";
val () = export_theory_no_docs ();
