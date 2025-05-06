open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2472Theory;
val () = new_theory "vfmTest2472";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2472") $ get_result_defs "vfmTestDefs2472";
val () = export_theory_no_docs ();
