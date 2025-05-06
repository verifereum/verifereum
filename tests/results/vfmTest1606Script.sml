open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1606Theory;
val () = new_theory "vfmTest1606";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1606") $ get_result_defs "vfmTestDefs1606";
val () = export_theory_no_docs ();
