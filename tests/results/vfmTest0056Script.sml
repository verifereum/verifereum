open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0056Theory;
val () = new_theory "vfmTest0056";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0056") $ get_result_defs "vfmTestDefs0056";
val () = export_theory_no_docs ();
