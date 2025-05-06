open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1168Theory;
val () = new_theory "vfmTest1168";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1168") $ get_result_defs "vfmTestDefs1168";
val () = export_theory_no_docs ();
