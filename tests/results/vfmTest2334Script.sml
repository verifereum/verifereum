open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2334Theory;
val () = new_theory "vfmTest2334";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2334") $ get_result_defs "vfmTestDefs2334";
val () = export_theory_no_docs ();
