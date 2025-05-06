open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1754Theory;
val () = new_theory "vfmTest1754";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1754") $ get_result_defs "vfmTestDefs1754";
val () = export_theory_no_docs ();
