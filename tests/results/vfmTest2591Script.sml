open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2591Theory;
val () = new_theory "vfmTest2591";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2591") $ get_result_defs "vfmTestDefs2591";
val () = export_theory_no_docs ();
