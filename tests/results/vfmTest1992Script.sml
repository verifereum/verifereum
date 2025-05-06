open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1992Theory;
val () = new_theory "vfmTest1992";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1992") $ get_result_defs "vfmTestDefs1992";
val () = export_theory_no_docs ();
