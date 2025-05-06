open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2402Theory;
val () = new_theory "vfmTest2402";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2402") $ get_result_defs "vfmTestDefs2402";
val () = export_theory_no_docs ();
