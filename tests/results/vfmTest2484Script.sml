open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2484Theory;
val () = new_theory "vfmTest2484";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2484") $ get_result_defs "vfmTestDefs2484";
val () = export_theory_no_docs ();
