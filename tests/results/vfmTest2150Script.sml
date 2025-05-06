open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2150Theory;
val () = new_theory "vfmTest2150";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2150") $ get_result_defs "vfmTestDefs2150";
val () = export_theory_no_docs ();
