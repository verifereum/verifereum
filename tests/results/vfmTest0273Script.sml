open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0273Theory;
val () = new_theory "vfmTest0273";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0273") $ get_result_defs "vfmTestDefs0273";
val () = export_theory_no_docs ();
