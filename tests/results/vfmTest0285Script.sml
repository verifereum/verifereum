open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0285Theory;
val () = new_theory "vfmTest0285";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0285") $ get_result_defs "vfmTestDefs0285";
val () = export_theory_no_docs ();
