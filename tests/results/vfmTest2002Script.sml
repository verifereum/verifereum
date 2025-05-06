open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2002Theory;
val () = new_theory "vfmTest2002";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2002") $ get_result_defs "vfmTestDefs2002";
val () = export_theory_no_docs ();
