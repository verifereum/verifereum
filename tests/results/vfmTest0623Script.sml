open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0623Theory;
val () = new_theory "vfmTest0623";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0623") $ get_result_defs "vfmTestDefs0623";
val () = export_theory_no_docs ();
