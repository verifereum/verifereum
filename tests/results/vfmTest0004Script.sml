open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0004Theory;
val () = new_theory "vfmTest0004";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0004") $ get_result_defs "vfmTestDefs0004";
val () = export_theory_no_docs ();
