open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1474Theory;
val () = new_theory "vfmTest1474";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1474") $ get_result_defs "vfmTestDefs1474";
val () = export_theory_no_docs ();
