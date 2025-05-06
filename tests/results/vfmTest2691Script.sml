open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2691Theory;
val () = new_theory "vfmTest2691";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2691") $ get_result_defs "vfmTestDefs2691";
val () = export_theory_no_docs ();
