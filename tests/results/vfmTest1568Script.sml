open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1568Theory;
val () = new_theory "vfmTest1568";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1568") $ get_result_defs "vfmTestDefs1568";
val () = export_theory_no_docs ();
