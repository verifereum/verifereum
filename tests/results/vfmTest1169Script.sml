open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1169Theory;
val () = new_theory "vfmTest1169";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1169") $ get_result_defs "vfmTestDefs1169";
val () = export_theory_no_docs ();
