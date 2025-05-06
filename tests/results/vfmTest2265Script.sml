open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2265Theory;
val () = new_theory "vfmTest2265";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2265") $ get_result_defs "vfmTestDefs2265";
val () = export_theory_no_docs ();
