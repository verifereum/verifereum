open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2471Theory;
val () = new_theory "vfmTest2471";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2471") $ get_result_defs "vfmTestDefs2471";
val () = export_theory_no_docs ();
