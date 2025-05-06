open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2469Theory;
val () = new_theory "vfmTest2469";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2469") $ get_result_defs "vfmTestDefs2469";
val () = export_theory_no_docs ();
