open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2047Theory;
val () = new_theory "vfmTest2047";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2047") $ get_result_defs "vfmTestDefs2047";
val () = export_theory_no_docs ();
