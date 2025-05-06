open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2438Theory;
val () = new_theory "vfmTest2438";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2438") $ get_result_defs "vfmTestDefs2438";
val () = export_theory_no_docs ();
