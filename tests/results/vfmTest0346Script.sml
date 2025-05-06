open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0346Theory;
val () = new_theory "vfmTest0346";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0346") $ get_result_defs "vfmTestDefs0346";
val () = export_theory_no_docs ();
