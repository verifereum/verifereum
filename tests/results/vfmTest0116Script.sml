open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0116Theory;
val () = new_theory "vfmTest0116";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0116") $ get_result_defs "vfmTestDefs0116";
val () = export_theory_no_docs ();
