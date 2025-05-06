open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0790Theory;
val () = new_theory "vfmTest0790";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0790") $ get_result_defs "vfmTestDefs0790";
val () = export_theory_no_docs ();
