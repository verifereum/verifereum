open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2777Theory;
val () = new_theory "vfmTest2777";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2777") $ get_result_defs "vfmTestDefs2777";
val () = export_theory_no_docs ();
