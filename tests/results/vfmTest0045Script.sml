open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0045Theory;
val () = new_theory "vfmTest0045";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0045") $ get_result_defs "vfmTestDefs0045";
val () = export_theory_no_docs ();
