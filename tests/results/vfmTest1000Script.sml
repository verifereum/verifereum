open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1000Theory;
val () = new_theory "vfmTest1000";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1000") $ get_result_defs "vfmTestDefs1000";
val () = export_theory_no_docs ();
