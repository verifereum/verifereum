open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2614Theory;
val () = new_theory "vfmTest2614";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2614") $ get_result_defs "vfmTestDefs2614";
val () = export_theory_no_docs ();
