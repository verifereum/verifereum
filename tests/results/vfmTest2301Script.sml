open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2301Theory;
val () = new_theory "vfmTest2301";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2301") $ get_result_defs "vfmTestDefs2301";
val () = export_theory_no_docs ();
