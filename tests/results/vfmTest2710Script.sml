open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2710Theory;
val () = new_theory "vfmTest2710";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2710") $ get_result_defs "vfmTestDefs2710";
val () = export_theory_no_docs ();
