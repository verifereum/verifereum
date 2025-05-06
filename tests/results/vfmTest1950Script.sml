open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1950Theory;
val () = new_theory "vfmTest1950";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1950") $ get_result_defs "vfmTestDefs1950";
val () = export_theory_no_docs ();
