open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2466Theory;
val () = new_theory "vfmTest2466";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2466") $ get_result_defs "vfmTestDefs2466";
val () = export_theory_no_docs ();
