open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0626Theory;
val () = new_theory "vfmTest0626";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0626") $ get_result_defs "vfmTestDefs0626";
val () = export_theory_no_docs ();
