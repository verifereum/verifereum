open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2191Theory;
val () = new_theory "vfmTest2191";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2191") $ get_result_defs "vfmTestDefs2191";
val () = export_theory_no_docs ();
