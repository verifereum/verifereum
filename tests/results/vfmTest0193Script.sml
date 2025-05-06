open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0193Theory;
val () = new_theory "vfmTest0193";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0193") $ get_result_defs "vfmTestDefs0193";
val () = export_theory_no_docs ();
