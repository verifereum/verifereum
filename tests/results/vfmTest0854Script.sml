open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0854Theory;
val () = new_theory "vfmTest0854";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0854") $ get_result_defs "vfmTestDefs0854";
val () = export_theory_no_docs ();
