open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0704Theory;
val () = new_theory "vfmTest0704";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0704") $ get_result_defs "vfmTestDefs0704";
val () = export_theory_no_docs ();
