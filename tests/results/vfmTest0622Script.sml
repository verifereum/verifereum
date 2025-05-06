open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0622Theory;
val () = new_theory "vfmTest0622";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0622") $ get_result_defs "vfmTestDefs0622";
val () = export_theory_no_docs ();
