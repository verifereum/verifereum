open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0591Theory;
val () = new_theory "vfmTest0591";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0591") $ get_result_defs "vfmTestDefs0591";
val () = export_theory_no_docs ();
