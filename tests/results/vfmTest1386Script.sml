open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1386Theory;
val () = new_theory "vfmTest1386";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1386") $ get_result_defs "vfmTestDefs1386";
val () = export_theory_no_docs ();
