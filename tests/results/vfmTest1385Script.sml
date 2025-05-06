open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1385Theory;
val () = new_theory "vfmTest1385";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1385") $ get_result_defs "vfmTestDefs1385";
val () = export_theory_no_docs ();
