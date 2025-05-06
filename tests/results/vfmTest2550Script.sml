open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2550Theory;
val () = new_theory "vfmTest2550";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2550") $ get_result_defs "vfmTestDefs2550";
val () = export_theory_no_docs ();
