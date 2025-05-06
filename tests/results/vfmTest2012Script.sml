open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2012Theory;
val () = new_theory "vfmTest2012";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2012") $ get_result_defs "vfmTestDefs2012";
val () = export_theory_no_docs ();
