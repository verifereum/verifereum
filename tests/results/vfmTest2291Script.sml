open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2291Theory;
val () = new_theory "vfmTest2291";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2291") $ get_result_defs "vfmTestDefs2291";
val () = export_theory_no_docs ();
