open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1232Theory;
val () = new_theory "vfmTest1232";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1232") $ get_result_defs "vfmTestDefs1232";
val () = export_theory_no_docs ();
