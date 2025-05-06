open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0412Theory;
val () = new_theory "vfmTest0412";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0412") $ get_result_defs "vfmTestDefs0412";
val () = export_theory_no_docs ();
