open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0775Theory;
val () = new_theory "vfmTest0775";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0775") $ get_result_defs "vfmTestDefs0775";
val () = export_theory_no_docs ();
