open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2677Theory;
val () = new_theory "vfmTest2677";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2677") $ get_result_defs "vfmTestDefs2677";
val () = export_theory_no_docs ();
