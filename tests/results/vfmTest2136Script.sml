open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2136Theory;
val () = new_theory "vfmTest2136";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2136") $ get_result_defs "vfmTestDefs2136";
val () = export_theory_no_docs ();
