open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0570Theory;
val () = new_theory "vfmTest0570";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0570") $ get_result_defs "vfmTestDefs0570";
val () = export_theory_no_docs ();
