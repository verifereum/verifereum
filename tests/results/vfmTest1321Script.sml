open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1321Theory;
val () = new_theory "vfmTest1321";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1321") $ get_result_defs "vfmTestDefs1321";
val () = export_theory_no_docs ();
