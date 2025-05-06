open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0249Theory;
val () = new_theory "vfmTest0249";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0249") $ get_result_defs "vfmTestDefs0249";
val () = export_theory_no_docs ();
