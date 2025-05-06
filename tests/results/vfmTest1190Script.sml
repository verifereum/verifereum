open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1190Theory;
val () = new_theory "vfmTest1190";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1190") $ get_result_defs "vfmTestDefs1190";
val () = export_theory_no_docs ();
