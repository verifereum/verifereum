open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2490Theory;
val () = new_theory "vfmTest2490";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2490") $ get_result_defs "vfmTestDefs2490";
val () = export_theory_no_docs ();
