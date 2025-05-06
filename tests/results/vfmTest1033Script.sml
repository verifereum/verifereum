open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1033Theory;
val () = new_theory "vfmTest1033";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1033") $ get_result_defs "vfmTestDefs1033";
val () = export_theory_no_docs ();
