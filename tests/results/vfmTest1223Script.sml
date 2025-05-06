open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1223Theory;
val () = new_theory "vfmTest1223";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1223") $ get_result_defs "vfmTestDefs1223";
val () = export_theory_no_docs ();
