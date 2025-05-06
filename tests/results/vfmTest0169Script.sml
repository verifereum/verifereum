open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0169Theory;
val () = new_theory "vfmTest0169";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0169") $ get_result_defs "vfmTestDefs0169";
val () = export_theory_no_docs ();
