open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0823Theory;
val () = new_theory "vfmTest0823";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0823") $ get_result_defs "vfmTestDefs0823";
val () = export_theory_no_docs ();
