open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2187Theory;
val () = new_theory "vfmTest2187";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2187") $ get_result_defs "vfmTestDefs2187";
val () = export_theory_no_docs ();
