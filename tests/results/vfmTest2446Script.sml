open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2446Theory;
val () = new_theory "vfmTest2446";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2446") $ get_result_defs "vfmTestDefs2446";
val () = export_theory_no_docs ();
