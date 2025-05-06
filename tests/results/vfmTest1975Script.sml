open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1975Theory;
val () = new_theory "vfmTest1975";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1975") $ get_result_defs "vfmTestDefs1975";
val () = export_theory_no_docs ();
