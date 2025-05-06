open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0886Theory;
val () = new_theory "vfmTest0886";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0886") $ get_result_defs "vfmTestDefs0886";
val () = export_theory_no_docs ();
