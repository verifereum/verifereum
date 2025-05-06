open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2567Theory;
val () = new_theory "vfmTest2567";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2567") $ get_result_defs "vfmTestDefs2567";
val () = export_theory_no_docs ();
