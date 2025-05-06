open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1200Theory;
val () = new_theory "vfmTest1200";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1200") $ get_result_defs "vfmTestDefs1200";
val () = export_theory_no_docs ();
