open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2449Theory;
val () = new_theory "vfmTest2449";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2449") $ get_result_defs "vfmTestDefs2449";
val () = export_theory_no_docs ();
