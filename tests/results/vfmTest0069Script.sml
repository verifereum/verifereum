open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0069Theory;
val () = new_theory "vfmTest0069";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0069") $ get_result_defs "vfmTestDefs0069";
val () = export_theory_no_docs ();
