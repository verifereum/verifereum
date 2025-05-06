open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1848Theory;
val () = new_theory "vfmTest1848";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1848") $ get_result_defs "vfmTestDefs1848";
val () = export_theory_no_docs ();
