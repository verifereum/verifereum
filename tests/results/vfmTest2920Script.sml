open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2920Theory;
val () = new_theory "vfmTest2920";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2920") $ get_result_defs "vfmTestDefs2920";
val () = export_theory_no_docs ();
