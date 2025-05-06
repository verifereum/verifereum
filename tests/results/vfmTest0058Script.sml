open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0058Theory;
val () = new_theory "vfmTest0058";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0058") $ get_result_defs "vfmTestDefs0058";
val () = export_theory_no_docs ();
