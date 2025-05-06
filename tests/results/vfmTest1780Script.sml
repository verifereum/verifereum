open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1780Theory;
val () = new_theory "vfmTest1780";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1780") $ get_result_defs "vfmTestDefs1780";
val () = export_theory_no_docs ();
