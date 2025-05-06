open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2396Theory;
val () = new_theory "vfmTest2396";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2396") $ get_result_defs "vfmTestDefs2396";
val () = export_theory_no_docs ();
