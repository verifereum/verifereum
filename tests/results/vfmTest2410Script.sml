open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2410Theory;
val () = new_theory "vfmTest2410";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2410") $ get_result_defs "vfmTestDefs2410";
val () = export_theory_no_docs ();
