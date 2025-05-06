open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1065Theory;
val () = new_theory "vfmTest1065";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1065") $ get_result_defs "vfmTestDefs1065";
val () = export_theory_no_docs ();
