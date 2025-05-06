open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1176Theory;
val () = new_theory "vfmTest1176";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1176") $ get_result_defs "vfmTestDefs1176";
val () = export_theory_no_docs ();
