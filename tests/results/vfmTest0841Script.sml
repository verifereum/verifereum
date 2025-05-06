open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0841Theory;
val () = new_theory "vfmTest0841";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0841") $ get_result_defs "vfmTestDefs0841";
val () = export_theory_no_docs ();
