open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0953Theory;
val () = new_theory "vfmTest0953";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0953") $ get_result_defs "vfmTestDefs0953";
val () = export_theory_no_docs ();
