open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1856Theory;
val () = new_theory "vfmTest1856";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1856") $ get_result_defs "vfmTestDefs1856";
val () = export_theory_no_docs ();
