open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1066Theory;
val () = new_theory "vfmTest1066";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1066") $ get_result_defs "vfmTestDefs1066";
val () = export_theory_no_docs ();
