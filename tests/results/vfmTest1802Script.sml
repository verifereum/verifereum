open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1802Theory;
val () = new_theory "vfmTest1802";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1802") $ get_result_defs "vfmTestDefs1802";
val () = export_theory_no_docs ();
