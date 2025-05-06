open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1261Theory;
val () = new_theory "vfmTest1261";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1261") $ get_result_defs "vfmTestDefs1261";
val () = export_theory_no_docs ();
