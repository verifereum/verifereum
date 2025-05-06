open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1835Theory;
val () = new_theory "vfmTest1835";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1835") $ get_result_defs "vfmTestDefs1835";
val () = export_theory_no_docs ();
