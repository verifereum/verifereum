open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0462Theory;
val () = new_theory "vfmTest0462";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0462") $ get_result_defs "vfmTestDefs0462";
val () = export_theory_no_docs ();
