open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2559Theory;
val () = new_theory "vfmTest2559";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2559") $ get_result_defs "vfmTestDefs2559";
val () = export_theory_no_docs ();
