open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0605Theory;
val () = new_theory "vfmTest0605";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0605") $ get_result_defs "vfmTestDefs0605";
val () = export_theory_no_docs ();
