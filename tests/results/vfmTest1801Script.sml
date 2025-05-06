open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1801Theory;
val () = new_theory "vfmTest1801";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1801") $ get_result_defs "vfmTestDefs1801";
val () = export_theory_no_docs ();
