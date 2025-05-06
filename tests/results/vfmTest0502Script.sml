open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0502Theory;
val () = new_theory "vfmTest0502";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0502") $ get_result_defs "vfmTestDefs0502";
val () = export_theory_no_docs ();
