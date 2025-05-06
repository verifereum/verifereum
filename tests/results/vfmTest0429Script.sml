open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0429Theory;
val () = new_theory "vfmTest0429";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0429") $ get_result_defs "vfmTestDefs0429";
val () = export_theory_no_docs ();
