open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2061Theory;
val () = new_theory "vfmTest2061";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2061") $ get_result_defs "vfmTestDefs2061";
val () = export_theory_no_docs ();
