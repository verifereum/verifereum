open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2345Theory;
val () = new_theory "vfmTest2345";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2345") $ get_result_defs "vfmTestDefs2345";
val () = export_theory_no_docs ();
