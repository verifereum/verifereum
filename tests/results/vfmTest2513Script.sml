open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2513Theory;
val () = new_theory "vfmTest2513";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2513") $ get_result_defs "vfmTestDefs2513";
val () = export_theory_no_docs ();
