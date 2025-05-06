open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0095Theory;
val () = new_theory "vfmTest0095";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0095") $ get_result_defs "vfmTestDefs0095";
val () = export_theory_no_docs ();
