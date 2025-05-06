open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1220Theory;
val () = new_theory "vfmTest1220";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1220") $ get_result_defs "vfmTestDefs1220";
val () = export_theory_no_docs ();
