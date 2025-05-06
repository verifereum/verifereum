open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0086Theory;
val () = new_theory "vfmTest0086";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0086") $ get_result_defs "vfmTestDefs0086";
val () = export_theory_no_docs ();
