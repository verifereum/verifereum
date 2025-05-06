open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2240Theory;
val () = new_theory "vfmTest2240";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2240") $ get_result_defs "vfmTestDefs2240";
val () = export_theory_no_docs ();
