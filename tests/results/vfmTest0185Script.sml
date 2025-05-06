open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0185Theory;
val () = new_theory "vfmTest0185";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0185") $ get_result_defs "vfmTestDefs0185";
val () = export_theory_no_docs ();
