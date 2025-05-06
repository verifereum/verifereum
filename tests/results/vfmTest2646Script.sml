open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs2646Theory;
val () = new_theory "vfmTest2646";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs2646") $ get_result_defs "vfmTestDefs2646";
val () = export_theory_no_docs ();
