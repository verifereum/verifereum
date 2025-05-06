open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0492Theory;
val () = new_theory "vfmTest0492";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0492") $ get_result_defs "vfmTestDefs0492";
val () = export_theory_no_docs ();
