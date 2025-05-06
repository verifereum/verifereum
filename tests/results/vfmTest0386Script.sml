open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0386Theory;
val () = new_theory "vfmTest0386";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0386") $ get_result_defs "vfmTestDefs0386";
val () = export_theory_no_docs ();
