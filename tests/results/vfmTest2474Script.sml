open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2474Theory;
val () = new_theory "vfmTest2474";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2474") $ get_result_defs "vfmTestDefs2474";
val () = export_theory_no_docs ();
