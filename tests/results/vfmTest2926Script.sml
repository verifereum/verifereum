open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2926Theory;
val () = new_theory "vfmTest2926";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2926") $ get_result_defs "vfmTestDefs2926";
val () = export_theory_no_docs ();
