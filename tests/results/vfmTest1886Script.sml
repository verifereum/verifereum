open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1886Theory;
val () = new_theory "vfmTest1886";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1886") $ get_result_defs "vfmTestDefs1886";
val () = export_theory_no_docs ();
