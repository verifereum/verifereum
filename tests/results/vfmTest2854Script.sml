open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2854Theory;
val () = new_theory "vfmTest2854";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2854") $ get_result_defs "vfmTestDefs2854";
val () = export_theory_no_docs ();
