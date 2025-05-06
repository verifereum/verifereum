open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1723Theory;
val () = new_theory "vfmTest1723";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1723") $ get_result_defs "vfmTestDefs1723";
val () = export_theory_no_docs ();
