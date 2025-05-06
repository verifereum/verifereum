open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2306Theory;
val () = new_theory "vfmTest2306";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2306") $ get_result_defs "vfmTestDefs2306";
val () = export_theory_no_docs ();
