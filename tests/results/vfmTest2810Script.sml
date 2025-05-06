open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2810Theory;
val () = new_theory "vfmTest2810";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2810") $ get_result_defs "vfmTestDefs2810";
val () = export_theory_no_docs ();
