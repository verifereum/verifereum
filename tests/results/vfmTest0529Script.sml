open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0529Theory;
val () = new_theory "vfmTest0529";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0529") $ get_result_defs "vfmTestDefs0529";
val () = export_theory_no_docs ();
