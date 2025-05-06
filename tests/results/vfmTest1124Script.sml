open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1124Theory;
val () = new_theory "vfmTest1124";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1124") $ get_result_defs "vfmTestDefs1124";
val () = export_theory_no_docs ();
