open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1845Theory;
val () = new_theory "vfmTest1845";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1845") $ get_result_defs "vfmTestDefs1845";
val () = export_theory_no_docs ();
