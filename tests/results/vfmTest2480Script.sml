open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2480Theory;
val () = new_theory "vfmTest2480";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2480") $ get_result_defs "vfmTestDefs2480";
val () = export_theory_no_docs ();
