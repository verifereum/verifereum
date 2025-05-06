open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1644Theory;
val () = new_theory "vfmTest1644";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1644") $ get_result_defs "vfmTestDefs1644";
val () = export_theory_no_docs ();
