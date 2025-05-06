open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0852Theory;
val () = new_theory "vfmTest0852";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0852") $ get_result_defs "vfmTestDefs0852";
val () = export_theory_no_docs ();
