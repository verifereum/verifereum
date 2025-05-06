open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2368Theory;
val () = new_theory "vfmTest2368";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2368") $ get_result_defs "vfmTestDefs2368";
val () = export_theory_no_docs ();
