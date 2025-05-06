open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0019Theory;
val () = new_theory "vfmTest0019";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0019") $ get_result_defs "vfmTestDefs0019";
val () = export_theory_no_docs ();
