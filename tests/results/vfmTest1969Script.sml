open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1969Theory;
val () = new_theory "vfmTest1969";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1969") $ get_result_defs "vfmTestDefs1969";
val () = export_theory_no_docs ();
