open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2021Theory;
val () = new_theory "vfmTest2021";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2021") $ get_result_defs "vfmTestDefs2021";
val () = export_theory_no_docs ();
