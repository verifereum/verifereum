open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2370Theory;
val () = new_theory "vfmTest2370";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2370") $ get_result_defs "vfmTestDefs2370";
val () = export_theory_no_docs ();
