open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1900Theory;
val () = new_theory "vfmTest1900";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1900") $ get_result_defs "vfmTestDefs1900";
val () = export_theory_no_docs ();
