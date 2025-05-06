open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1490Theory;
val () = new_theory "vfmTest1490";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1490") $ get_result_defs "vfmTestDefs1490";
val () = export_theory_no_docs ();
