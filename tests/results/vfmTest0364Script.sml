open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0364Theory;
val () = new_theory "vfmTest0364";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0364") $ get_result_defs "vfmTestDefs0364";
val () = export_theory_no_docs ();
