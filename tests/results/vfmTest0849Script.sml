open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0849Theory;
val () = new_theory "vfmTest0849";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0849") $ get_result_defs "vfmTestDefs0849";
val () = export_theory_no_docs ();
