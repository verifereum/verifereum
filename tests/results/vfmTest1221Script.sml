open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1221Theory;
val () = new_theory "vfmTest1221";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1221") $ get_result_defs "vfmTestDefs1221";
val () = export_theory_no_docs ();
