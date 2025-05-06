open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0032Theory;
val () = new_theory "vfmTest0032";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0032") $ get_result_defs "vfmTestDefs0032";
val () = export_theory_no_docs ();
