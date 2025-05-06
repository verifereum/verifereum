open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1210Theory;
val () = new_theory "vfmTest1210";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1210") $ get_result_defs "vfmTestDefs1210";
val () = export_theory_no_docs ();
