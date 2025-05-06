open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1171Theory;
val () = new_theory "vfmTest1171";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1171") $ get_result_defs "vfmTestDefs1171";
val () = export_theory_no_docs ();
