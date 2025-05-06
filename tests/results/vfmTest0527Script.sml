open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0527Theory;
val () = new_theory "vfmTest0527";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0527") $ get_result_defs "vfmTestDefs0527";
val () = export_theory_no_docs ();
