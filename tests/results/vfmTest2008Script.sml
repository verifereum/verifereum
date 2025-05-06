open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2008Theory;
val () = new_theory "vfmTest2008";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2008") $ get_result_defs "vfmTestDefs2008";
val () = export_theory_no_docs ();
