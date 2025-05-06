open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1763Theory;
val () = new_theory "vfmTest1763";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1763") $ get_result_defs "vfmTestDefs1763";
val () = export_theory_no_docs ();
