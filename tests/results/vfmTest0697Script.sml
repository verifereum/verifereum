open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0697Theory;
val () = new_theory "vfmTest0697";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0697") $ get_result_defs "vfmTestDefs0697";
val () = export_theory_no_docs ();
