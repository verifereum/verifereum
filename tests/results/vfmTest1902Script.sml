open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1902Theory;
val () = new_theory "vfmTest1902";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1902") $ get_result_defs "vfmTestDefs1902";
val () = export_theory_no_docs ();
