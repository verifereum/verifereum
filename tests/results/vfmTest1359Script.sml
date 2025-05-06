open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1359Theory;
val () = new_theory "vfmTest1359";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1359") $ get_result_defs "vfmTestDefs1359";
val () = export_theory_no_docs ();
