open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2853Theory;
val () = new_theory "vfmTest2853";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2853") $ get_result_defs "vfmTestDefs2853";
val () = export_theory_no_docs ();
