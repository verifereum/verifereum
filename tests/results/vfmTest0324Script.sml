open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0324Theory;
val () = new_theory "vfmTest0324";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0324") $ get_result_defs "vfmTestDefs0324";
val () = export_theory_no_docs ();
