open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0098Theory;
val () = new_theory "vfmTest0098";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0098") $ get_result_defs "vfmTestDefs0098";
val () = export_theory_no_docs ();
