open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1110Theory;
val () = new_theory "vfmTest1110";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1110") $ get_result_defs "vfmTestDefs1110";
val () = export_theory_no_docs ();
