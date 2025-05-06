open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2769Theory;
val () = new_theory "vfmTest2769";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2769") $ get_result_defs "vfmTestDefs2769";
val () = export_theory_no_docs ();
