open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0617Theory;
val () = new_theory "vfmTest0617";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0617") $ get_result_defs "vfmTestDefs0617";
val () = export_theory_no_docs ();
