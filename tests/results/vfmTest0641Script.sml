open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0641Theory;
val () = new_theory "vfmTest0641";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0641") $ get_result_defs "vfmTestDefs0641";
val () = export_theory_no_docs ();
