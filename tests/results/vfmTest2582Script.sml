open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2582Theory;
val () = new_theory "vfmTest2582";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2582") $ get_result_defs "vfmTestDefs2582";
val () = export_theory_no_docs ();
