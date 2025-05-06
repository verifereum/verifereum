open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0632Theory;
val () = new_theory "vfmTest0632";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0632") $ get_result_defs "vfmTestDefs0632";
val () = export_theory_no_docs ();
