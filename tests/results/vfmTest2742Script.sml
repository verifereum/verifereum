open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2742Theory;
val () = new_theory "vfmTest2742";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2742") $ get_result_defs "vfmTestDefs2742";
val () = export_theory_no_docs ();
