open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2383Theory;
val () = new_theory "vfmTest2383";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2383") $ get_result_defs "vfmTestDefs2383";
val () = export_theory_no_docs ();
