open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0791Theory;
val () = new_theory "vfmTest0791";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0791") $ get_result_defs "vfmTestDefs0791";
val () = export_theory_no_docs ();
