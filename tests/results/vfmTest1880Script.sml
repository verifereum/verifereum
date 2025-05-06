open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1880Theory;
val () = new_theory "vfmTest1880";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1880") $ get_result_defs "vfmTestDefs1880";
val () = export_theory_no_docs ();
