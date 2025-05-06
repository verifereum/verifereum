open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0321Theory;
val () = new_theory "vfmTest0321";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0321") $ get_result_defs "vfmTestDefs0321";
val () = export_theory_no_docs ();
