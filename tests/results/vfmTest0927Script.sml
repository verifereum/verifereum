open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0927Theory;
val () = new_theory "vfmTest0927";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0927") $ get_result_defs "vfmTestDefs0927";
val () = export_theory_no_docs ();
