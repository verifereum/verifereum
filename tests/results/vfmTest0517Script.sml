open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0517Theory;
val () = new_theory "vfmTest0517";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0517") $ get_result_defs "vfmTestDefs0517";
val () = export_theory_no_docs ();
