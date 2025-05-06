open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2266Theory;
val () = new_theory "vfmTest2266";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2266") $ get_result_defs "vfmTestDefs2266";
val () = export_theory_no_docs ();
