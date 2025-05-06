open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2506Theory;
val () = new_theory "vfmTest2506";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2506") $ get_result_defs "vfmTestDefs2506";
val () = export_theory_no_docs ();
