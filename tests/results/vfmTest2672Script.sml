open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2672Theory;
val () = new_theory "vfmTest2672";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2672") $ get_result_defs "vfmTestDefs2672";
val () = export_theory_no_docs ();
