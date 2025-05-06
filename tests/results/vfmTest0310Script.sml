open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0310Theory;
val () = new_theory "vfmTest0310";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0310") $ get_result_defs "vfmTestDefs0310";
val () = export_theory_no_docs ();
