open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0136Theory;
val () = new_theory "vfmTest0136";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0136") $ get_result_defs "vfmTestDefs0136";
val () = export_theory_no_docs ();
