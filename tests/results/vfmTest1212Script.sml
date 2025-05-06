open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1212Theory;
val () = new_theory "vfmTest1212";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1212") $ get_result_defs "vfmTestDefs1212";
val () = export_theory_no_docs ();
