open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2130Theory;
val () = new_theory "vfmTest2130";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2130") $ get_result_defs "vfmTestDefs2130";
val () = export_theory_no_docs ();
