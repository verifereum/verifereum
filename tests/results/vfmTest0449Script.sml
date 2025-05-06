open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0449Theory;
val () = new_theory "vfmTest0449";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0449") $ get_result_defs "vfmTestDefs0449";
val () = export_theory_no_docs ();
