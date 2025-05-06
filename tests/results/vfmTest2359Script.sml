open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2359Theory;
val () = new_theory "vfmTest2359";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2359") $ get_result_defs "vfmTestDefs2359";
val () = export_theory_no_docs ();
