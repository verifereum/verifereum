open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0176Theory;
val () = new_theory "vfmTest0176";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0176") $ get_result_defs "vfmTestDefs0176";
val () = export_theory_no_docs ();
