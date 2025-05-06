open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0773Theory;
val () = new_theory "vfmTest0773";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0773") $ get_result_defs "vfmTestDefs0773";
val () = export_theory_no_docs ();
