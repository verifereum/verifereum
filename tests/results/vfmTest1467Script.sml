open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1467Theory;
val () = new_theory "vfmTest1467";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1467") $ get_result_defs "vfmTestDefs1467";
val () = export_theory_no_docs ();
