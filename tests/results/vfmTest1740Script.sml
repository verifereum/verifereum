open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1740Theory;
val () = new_theory "vfmTest1740";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1740") $ get_result_defs "vfmTestDefs1740";
val () = export_theory_no_docs ();
