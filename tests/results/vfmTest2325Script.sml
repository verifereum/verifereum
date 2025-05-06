open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2325Theory;
val () = new_theory "vfmTest2325";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2325") $ get_result_defs "vfmTestDefs2325";
val () = export_theory_no_docs ();
