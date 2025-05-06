open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0039Theory;
val () = new_theory "vfmTest0039";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0039") $ get_result_defs "vfmTestDefs0039";
val () = export_theory_no_docs ();
