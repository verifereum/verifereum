open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1219Theory;
val () = new_theory "vfmTest1219";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1219") $ get_result_defs "vfmTestDefs1219";
val () = export_theory_no_docs ();
