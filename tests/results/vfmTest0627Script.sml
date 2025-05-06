open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0627Theory;
val () = new_theory "vfmTest0627";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0627") $ get_result_defs "vfmTestDefs0627";
val () = export_theory_no_docs ();
