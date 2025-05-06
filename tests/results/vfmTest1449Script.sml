open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1449Theory;
val () = new_theory "vfmTest1449";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1449") $ get_result_defs "vfmTestDefs1449";
val () = export_theory_no_docs ();
