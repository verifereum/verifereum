open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1613Theory;
val () = new_theory "vfmTest1613";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1613") $ get_result_defs "vfmTestDefs1613";
val () = export_theory_no_docs ();
