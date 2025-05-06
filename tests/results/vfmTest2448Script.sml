open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2448Theory;
val () = new_theory "vfmTest2448";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2448") $ get_result_defs "vfmTestDefs2448";
val () = export_theory_no_docs ();
