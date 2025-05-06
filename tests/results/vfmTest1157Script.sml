open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1157Theory;
val () = new_theory "vfmTest1157";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1157") $ get_result_defs "vfmTestDefs1157";
val () = export_theory_no_docs ();
