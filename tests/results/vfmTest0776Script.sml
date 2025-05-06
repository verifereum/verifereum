open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0776Theory;
val () = new_theory "vfmTest0776";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0776") $ get_result_defs "vfmTestDefs0776";
val () = export_theory_no_docs ();
