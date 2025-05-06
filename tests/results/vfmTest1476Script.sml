open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1476Theory;
val () = new_theory "vfmTest1476";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1476") $ get_result_defs "vfmTestDefs1476";
val () = export_theory_no_docs ();
