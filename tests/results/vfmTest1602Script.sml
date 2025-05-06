open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1602Theory;
val () = new_theory "vfmTest1602";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1602") $ get_result_defs "vfmTestDefs1602";
val () = export_theory_no_docs ();
