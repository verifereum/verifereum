open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1172Theory;
val () = new_theory "vfmTest1172";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1172") $ get_result_defs "vfmTestDefs1172";
val () = export_theory_no_docs ();
