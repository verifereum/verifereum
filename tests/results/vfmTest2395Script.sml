open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2395Theory;
val () = new_theory "vfmTest2395";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2395") $ get_result_defs "vfmTestDefs2395";
val () = export_theory_no_docs ();
