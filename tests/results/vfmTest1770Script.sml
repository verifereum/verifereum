open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1770Theory;
val () = new_theory "vfmTest1770";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1770") $ get_result_defs "vfmTestDefs1770";
val () = export_theory_no_docs ();
