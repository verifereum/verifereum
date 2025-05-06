open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0349Theory;
val () = new_theory "vfmTest0349";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0349") $ get_result_defs "vfmTestDefs0349";
val () = export_theory_no_docs ();
