open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2697Theory;
val () = new_theory "vfmTest2697";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2697") $ get_result_defs "vfmTestDefs2697";
val () = export_theory_no_docs ();
