open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0993Theory;
val () = new_theory "vfmTest0993";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0993") $ get_result_defs "vfmTestDefs0993";
val () = export_theory_no_docs ();
