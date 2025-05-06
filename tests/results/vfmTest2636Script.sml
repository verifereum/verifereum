open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2636Theory;
val () = new_theory "vfmTest2636";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2636") $ get_result_defs "vfmTestDefs2636";
val () = export_theory_no_docs ();
