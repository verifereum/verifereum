open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0063Theory;
val () = new_theory "vfmTest0063";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0063") $ get_result_defs "vfmTestDefs0063";
val () = export_theory_no_docs ();
