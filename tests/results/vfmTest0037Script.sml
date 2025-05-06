open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0037Theory;
val () = new_theory "vfmTest0037";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0037") $ get_result_defs "vfmTestDefs0037";
val () = export_theory_no_docs ();
