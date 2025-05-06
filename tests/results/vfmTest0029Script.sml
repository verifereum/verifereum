open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0029Theory;
val () = new_theory "vfmTest0029";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0029") $ get_result_defs "vfmTestDefs0029";
val () = export_theory_no_docs ();
