open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2800Theory;
val () = new_theory "vfmTest2800";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2800") $ get_result_defs "vfmTestDefs2800";
val () = export_theory_no_docs ();
