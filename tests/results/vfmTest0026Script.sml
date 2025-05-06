open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0026Theory;
val () = new_theory "vfmTest0026";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0026") $ get_result_defs "vfmTestDefs0026";
val () = export_theory_no_docs ();
