open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0696Theory;
val () = new_theory "vfmTest0696";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0696") $ get_result_defs "vfmTestDefs0696";
val () = export_theory_no_docs ();
