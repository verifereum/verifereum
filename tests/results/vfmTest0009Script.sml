open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0009Theory;
val () = new_theory "vfmTest0009";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0009") $ get_result_defs "vfmTestDefs0009";
val () = export_theory_no_docs ();
