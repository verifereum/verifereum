open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1402Theory;
val () = new_theory "vfmTest1402";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1402") $ get_result_defs "vfmTestDefs1402";
val () = export_theory_no_docs ();
