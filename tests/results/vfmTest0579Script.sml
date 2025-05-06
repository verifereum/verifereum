open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0579Theory;
val () = new_theory "vfmTest0579";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0579") $ get_result_defs "vfmTestDefs0579";
val () = export_theory_no_docs ();
