open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0601Theory;
val () = new_theory "vfmTest0601";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0601") $ get_result_defs "vfmTestDefs0601";
val () = export_theory_no_docs ();
