open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs1994Theory;
val () = new_theory "vfmTest1994";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs1994") $ get_result_defs "vfmTestDefs1994";
val () = export_theory_no_docs ();
