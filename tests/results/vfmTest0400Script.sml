open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0400Theory;
val () = new_theory "vfmTest0400";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0400") $ get_result_defs "vfmTestDefs0400";
val () = export_theory_no_docs ();
