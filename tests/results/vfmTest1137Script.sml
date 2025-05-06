open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1137Theory;
val () = new_theory "vfmTest1137";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1137") $ get_result_defs "vfmTestDefs1137";
val () = export_theory_no_docs ();
