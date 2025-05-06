open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1459Theory;
val () = new_theory "vfmTest1459";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1459") $ get_result_defs "vfmTestDefs1459";
val () = export_theory_no_docs ();
