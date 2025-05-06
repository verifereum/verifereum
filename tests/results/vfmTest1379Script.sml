open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1379Theory;
val () = new_theory "vfmTest1379";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1379") $ get_result_defs "vfmTestDefs1379";
val () = export_theory_no_docs ();
