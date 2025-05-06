open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0124Theory;
val () = new_theory "vfmTest0124";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0124") $ get_result_defs "vfmTestDefs0124";
val () = export_theory_no_docs ();
