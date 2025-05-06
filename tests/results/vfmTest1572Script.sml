open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1572Theory;
val () = new_theory "vfmTest1572";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1572") $ get_result_defs "vfmTestDefs1572";
val () = export_theory_no_docs ();
