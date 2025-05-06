open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1079Theory;
val () = new_theory "vfmTest1079";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1079") $ get_result_defs "vfmTestDefs1079";
val () = export_theory_no_docs ();
