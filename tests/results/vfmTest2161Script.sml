open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2161Theory;
val () = new_theory "vfmTest2161";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2161") $ get_result_defs "vfmTestDefs2161";
val () = export_theory_no_docs ();
