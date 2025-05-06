open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1929Theory;
val () = new_theory "vfmTest1929";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1929") $ get_result_defs "vfmTestDefs1929";
val () = export_theory_no_docs ();
