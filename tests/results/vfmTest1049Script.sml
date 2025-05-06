open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1049Theory;
val () = new_theory "vfmTest1049";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1049") $ get_result_defs "vfmTestDefs1049";
val () = export_theory_no_docs ();
