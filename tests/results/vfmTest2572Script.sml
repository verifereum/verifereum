open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2572Theory;
val () = new_theory "vfmTest2572";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2572") $ get_result_defs "vfmTestDefs2572";
val () = export_theory_no_docs ();
