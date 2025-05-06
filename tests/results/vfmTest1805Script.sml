open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1805Theory;
val () = new_theory "vfmTest1805";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1805") $ get_result_defs "vfmTestDefs1805";
val () = export_theory_no_docs ();
