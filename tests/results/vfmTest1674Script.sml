open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1674Theory;
val () = new_theory "vfmTest1674";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1674") $ get_result_defs "vfmTestDefs1674";
val () = export_theory_no_docs ();
