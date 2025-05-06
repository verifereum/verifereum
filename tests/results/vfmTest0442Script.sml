open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0442Theory;
val () = new_theory "vfmTest0442";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0442") $ get_result_defs "vfmTestDefs0442";
val () = export_theory_no_docs ();
