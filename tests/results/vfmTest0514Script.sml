open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0514Theory;
val () = new_theory "vfmTest0514";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0514") $ get_result_defs "vfmTestDefs0514";
val () = export_theory_no_docs ();
