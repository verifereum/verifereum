open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0333Theory;
val () = new_theory "vfmTest0333";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0333") $ get_result_defs "vfmTestDefs0333";
val () = export_theory_no_docs ();
