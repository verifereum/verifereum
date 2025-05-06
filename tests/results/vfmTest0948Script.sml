open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0948Theory;
val () = new_theory "vfmTest0948";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0948") $ get_result_defs "vfmTestDefs0948";
val () = export_theory_no_docs ();
