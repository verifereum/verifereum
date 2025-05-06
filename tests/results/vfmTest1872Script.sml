open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1872Theory;
val () = new_theory "vfmTest1872";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1872") $ get_result_defs "vfmTestDefs1872";
val () = export_theory_no_docs ();
