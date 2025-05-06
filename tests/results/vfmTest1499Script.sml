open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1499Theory;
val () = new_theory "vfmTest1499";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1499") $ get_result_defs "vfmTestDefs1499";
val () = export_theory_no_docs ();
