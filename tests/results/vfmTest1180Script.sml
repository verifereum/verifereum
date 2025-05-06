open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1180Theory;
val () = new_theory "vfmTest1180";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1180") $ get_result_defs "vfmTestDefs1180";
val () = export_theory_no_docs ();
