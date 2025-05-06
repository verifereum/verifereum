open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1278Theory;
val () = new_theory "vfmTest1278";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1278") $ get_result_defs "vfmTestDefs1278";
val () = export_theory_no_docs ();
