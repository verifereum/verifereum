open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1330Theory;
val () = new_theory "vfmTest1330";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1330") $ get_result_defs "vfmTestDefs1330";
val () = export_theory_no_docs ();
