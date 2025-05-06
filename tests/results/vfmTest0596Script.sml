open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0596Theory;
val () = new_theory "vfmTest0596";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0596") $ get_result_defs "vfmTestDefs0596";
val () = export_theory_no_docs ();
