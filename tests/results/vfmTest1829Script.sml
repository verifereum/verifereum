open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1829Theory;
val () = new_theory "vfmTest1829";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1829") $ get_result_defs "vfmTestDefs1829";
val () = export_theory_no_docs ();
