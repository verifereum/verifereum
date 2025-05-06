open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2118Theory;
val () = new_theory "vfmTest2118";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2118") $ get_result_defs "vfmTestDefs2118";
val () = export_theory_no_docs ();
