open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1917Theory;
val () = new_theory "vfmTest1917";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1917") $ get_result_defs "vfmTestDefs1917";
val () = export_theory_no_docs ();
