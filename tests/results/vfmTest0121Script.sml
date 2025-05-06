open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0121Theory;
val () = new_theory "vfmTest0121";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0121") $ get_result_defs "vfmTestDefs0121";
val () = export_theory_no_docs ();
