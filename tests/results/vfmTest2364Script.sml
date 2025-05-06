open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2364Theory;
val () = new_theory "vfmTest2364";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2364") $ get_result_defs "vfmTestDefs2364";
val () = export_theory_no_docs ();
