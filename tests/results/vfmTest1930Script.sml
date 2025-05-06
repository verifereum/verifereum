open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1930Theory;
val () = new_theory "vfmTest1930";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1930") $ get_result_defs "vfmTestDefs1930";
val () = export_theory_no_docs ();
