open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2363Theory;
val () = new_theory "vfmTest2363";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2363") $ get_result_defs "vfmTestDefs2363";
val () = export_theory_no_docs ();
