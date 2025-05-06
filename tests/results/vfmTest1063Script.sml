open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1063Theory;
val () = new_theory "vfmTest1063";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1063") $ get_result_defs "vfmTestDefs1063";
val () = export_theory_no_docs ();
