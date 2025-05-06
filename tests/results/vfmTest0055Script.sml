open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0055Theory;
val () = new_theory "vfmTest0055";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0055") $ get_result_defs "vfmTestDefs0055";
val () = export_theory_no_docs ();
