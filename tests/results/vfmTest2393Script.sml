open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2393Theory;
val () = new_theory "vfmTest2393";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2393") $ get_result_defs "vfmTestDefs2393";
val () = export_theory_no_docs ();
