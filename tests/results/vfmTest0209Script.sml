open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0209Theory;
val () = new_theory "vfmTest0209";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0209") $ get_result_defs "vfmTestDefs0209";
val () = export_theory_no_docs ();
