open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2502Theory;
val () = new_theory "vfmTest2502";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2502") $ get_result_defs "vfmTestDefs2502";
val () = export_theory_no_docs ();
