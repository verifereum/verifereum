open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0025Theory;
val () = new_theory "vfmTest0025";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0025") $ get_result_defs "vfmTestDefs0025";
val () = export_theory_no_docs ();
