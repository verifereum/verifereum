open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0748Theory;
val () = new_theory "vfmTest0748";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0748") $ get_result_defs "vfmTestDefs0748";
val () = export_theory_no_docs ();
