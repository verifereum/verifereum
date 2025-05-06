open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0499Theory;
val () = new_theory "vfmTest0499";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0499") $ get_result_defs "vfmTestDefs0499";
val () = export_theory_no_docs ();
