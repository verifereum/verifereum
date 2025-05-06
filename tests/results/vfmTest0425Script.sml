open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0425Theory;
val () = new_theory "vfmTest0425";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0425") $ get_result_defs "vfmTestDefs0425";
val () = export_theory_no_docs ();
