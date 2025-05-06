open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0123Theory;
val () = new_theory "vfmTest0123";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0123") $ get_result_defs "vfmTestDefs0123";
val () = export_theory_no_docs ();
