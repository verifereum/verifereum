open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0405Theory;
val () = new_theory "vfmTest0405";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0405") $ get_result_defs "vfmTestDefs0405";
val () = export_theory_no_docs ();
