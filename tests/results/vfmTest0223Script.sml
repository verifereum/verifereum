open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0223Theory;
val () = new_theory "vfmTest0223";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0223") $ get_result_defs "vfmTestDefs0223";
val () = export_theory_no_docs ();
