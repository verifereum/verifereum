open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0363Theory;
val () = new_theory "vfmTest0363";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0363") $ get_result_defs "vfmTestDefs0363";
val () = export_theory_no_docs ();
