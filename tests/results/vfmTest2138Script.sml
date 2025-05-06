open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2138Theory;
val () = new_theory "vfmTest2138";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2138") $ get_result_defs "vfmTestDefs2138";
val () = export_theory_no_docs ();
