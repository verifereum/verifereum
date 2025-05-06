open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0050Theory;
val () = new_theory "vfmTest0050";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0050") $ get_result_defs "vfmTestDefs0050";
val () = export_theory_no_docs ();
