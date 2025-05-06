open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2226Theory;
val () = new_theory "vfmTest2226";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2226") $ get_result_defs "vfmTestDefs2226";
val () = export_theory_no_docs ();
