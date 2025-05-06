open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0257Theory;
val () = new_theory "vfmTest0257";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0257") $ get_result_defs "vfmTestDefs0257";
val () = export_theory_no_docs ();
