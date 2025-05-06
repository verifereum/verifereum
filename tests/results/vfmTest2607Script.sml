open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2607Theory;
val () = new_theory "vfmTest2607";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2607") $ get_result_defs "vfmTestDefs2607";
val () = export_theory_no_docs ();
