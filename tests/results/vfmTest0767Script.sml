open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0767Theory;
val () = new_theory "vfmTest0767";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0767") $ get_result_defs "vfmTestDefs0767";
val () = export_theory_no_docs ();
