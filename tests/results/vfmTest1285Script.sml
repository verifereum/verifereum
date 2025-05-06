open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1285Theory;
val () = new_theory "vfmTest1285";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1285") $ get_result_defs "vfmTestDefs1285";
val () = export_theory_no_docs ();
