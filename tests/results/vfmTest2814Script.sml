open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2814Theory;
val () = new_theory "vfmTest2814";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2814") $ get_result_defs "vfmTestDefs2814";
val () = export_theory_no_docs ();
