open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2093Theory;
val () = new_theory "vfmTest2093";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2093") $ get_result_defs "vfmTestDefs2093";
val () = export_theory_no_docs ();
