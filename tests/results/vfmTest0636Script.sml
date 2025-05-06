open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0636Theory;
val () = new_theory "vfmTest0636";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0636") $ get_result_defs "vfmTestDefs0636";
val () = export_theory_no_docs ();
