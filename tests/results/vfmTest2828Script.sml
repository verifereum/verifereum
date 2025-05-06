open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2828Theory;
val () = new_theory "vfmTest2828";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2828") $ get_result_defs "vfmTestDefs2828";
val () = export_theory_no_docs ();
