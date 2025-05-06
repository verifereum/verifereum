open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2637Theory;
val () = new_theory "vfmTest2637";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2637") $ get_result_defs "vfmTestDefs2637";
val () = export_theory_no_docs ();
