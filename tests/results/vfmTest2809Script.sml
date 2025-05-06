open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2809Theory;
val () = new_theory "vfmTest2809";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2809") $ get_result_defs "vfmTestDefs2809";
val () = export_theory_no_docs ();
