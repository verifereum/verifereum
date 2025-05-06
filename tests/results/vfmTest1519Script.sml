open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1519Theory;
val () = new_theory "vfmTest1519";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1519") $ get_result_defs "vfmTestDefs1519";
val () = export_theory_no_docs ();
