open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0788Theory;
val () = new_theory "vfmTest0788";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0788") $ get_result_defs "vfmTestDefs0788";
val () = export_theory_no_docs ();
