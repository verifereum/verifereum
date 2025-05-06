open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2148Theory;
val () = new_theory "vfmTest2148";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2148") $ get_result_defs "vfmTestDefs2148";
val () = export_theory_no_docs ();
