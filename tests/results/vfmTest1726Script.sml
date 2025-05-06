open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1726Theory;
val () = new_theory "vfmTest1726";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1726") $ get_result_defs "vfmTestDefs1726";
val () = export_theory_no_docs ();
