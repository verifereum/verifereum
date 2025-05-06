open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0872Theory;
val () = new_theory "vfmTest0872";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0872") $ get_result_defs "vfmTestDefs0872";
val () = export_theory_no_docs ();
