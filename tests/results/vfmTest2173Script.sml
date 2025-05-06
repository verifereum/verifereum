open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2173Theory;
val () = new_theory "vfmTest2173";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2173") $ get_result_defs "vfmTestDefs2173";
val () = export_theory_no_docs ();
