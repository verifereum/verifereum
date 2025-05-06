open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2194Theory;
val () = new_theory "vfmTest2194";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2194") $ get_result_defs "vfmTestDefs2194";
val () = export_theory_no_docs ();
