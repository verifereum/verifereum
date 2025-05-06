open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1638Theory;
val () = new_theory "vfmTest1638";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1638") $ get_result_defs "vfmTestDefs1638";
val () = export_theory_no_docs ();
