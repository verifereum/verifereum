open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0537Theory;
val () = new_theory "vfmTest0537";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0537") $ get_result_defs "vfmTestDefs0537";
val () = export_theory_no_docs ();
