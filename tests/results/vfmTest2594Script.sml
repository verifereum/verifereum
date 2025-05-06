open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2594Theory;
val () = new_theory "vfmTest2594";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2594") $ get_result_defs "vfmTestDefs2594";
val () = export_theory_no_docs ();
