open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0296Theory;
val () = new_theory "vfmTest0296";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0296") $ get_result_defs "vfmTestDefs0296";
val () = export_theory_no_docs ();
