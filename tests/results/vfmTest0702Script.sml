open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0702Theory;
val () = new_theory "vfmTest0702";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0702") $ get_result_defs "vfmTestDefs0702";
val () = export_theory_no_docs ();
