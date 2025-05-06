open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0699Theory;
val () = new_theory "vfmTest0699";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0699") $ get_result_defs "vfmTestDefs0699";
val () = export_theory_no_docs ();
