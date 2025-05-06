open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2861Theory;
val () = new_theory "vfmTest2861";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2861") $ get_result_defs "vfmTestDefs2861";
val () = export_theory_no_docs ();
