open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2256Theory;
val () = new_theory "vfmTest2256";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2256") $ get_result_defs "vfmTestDefs2256";
val () = export_theory_no_docs ();
