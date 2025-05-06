open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1096Theory;
val () = new_theory "vfmTest1096";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1096") $ get_result_defs "vfmTestDefs1096";
val () = export_theory_no_docs ();
