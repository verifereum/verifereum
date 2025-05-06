open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2209Theory;
val () = new_theory "vfmTest2209";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2209") $ get_result_defs "vfmTestDefs2209";
val () = export_theory_no_docs ();
