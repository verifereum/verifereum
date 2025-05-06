open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0240Theory;
val () = new_theory "vfmTest0240";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0240") $ get_result_defs "vfmTestDefs0240";
val () = export_theory_no_docs ();
