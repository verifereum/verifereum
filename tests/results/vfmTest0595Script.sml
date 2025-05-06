open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0595Theory;
val () = new_theory "vfmTest0595";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0595") $ get_result_defs "vfmTestDefs0595";
val () = export_theory_no_docs ();
