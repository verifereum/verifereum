open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2001Theory;
val () = new_theory "vfmTest2001";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2001") $ get_result_defs "vfmTestDefs2001";
val () = export_theory_no_docs ();
