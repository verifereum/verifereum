open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0450Theory;
val () = new_theory "vfmTest0450";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0450") $ get_result_defs "vfmTestDefs0450";
val () = export_theory_no_docs ();
