open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1314Theory;
val () = new_theory "vfmTest1314";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1314") $ get_result_defs "vfmTestDefs1314";
val () = export_theory_no_docs ();
