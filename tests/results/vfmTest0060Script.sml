open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0060Theory;
val () = new_theory "vfmTest0060";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0060") $ get_result_defs "vfmTestDefs0060";
val () = export_theory_no_docs ();
