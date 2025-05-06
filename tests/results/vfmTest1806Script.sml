open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1806Theory;
val () = new_theory "vfmTest1806";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1806") $ get_result_defs "vfmTestDefs1806";
val () = export_theory_no_docs ();
