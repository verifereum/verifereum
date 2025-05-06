open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2239Theory;
val () = new_theory "vfmTest2239";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2239") $ get_result_defs "vfmTestDefs2239";
val () = export_theory_no_docs ();
