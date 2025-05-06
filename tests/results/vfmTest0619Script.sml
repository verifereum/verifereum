open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0619Theory;
val () = new_theory "vfmTest0619";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0619") $ get_result_defs "vfmTestDefs0619";
val () = export_theory_no_docs ();
