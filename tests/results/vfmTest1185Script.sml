open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1185Theory;
val () = new_theory "vfmTest1185";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1185") $ get_result_defs "vfmTestDefs1185";
val () = export_theory_no_docs ();
