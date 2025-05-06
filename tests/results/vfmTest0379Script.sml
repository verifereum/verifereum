open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0379Theory;
val () = new_theory "vfmTest0379";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0379") $ get_result_defs "vfmTestDefs0379";
val () = export_theory_no_docs ();
