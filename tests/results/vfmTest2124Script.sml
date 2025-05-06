open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2124Theory;
val () = new_theory "vfmTest2124";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2124") $ get_result_defs "vfmTestDefs2124";
val () = export_theory_no_docs ();
