open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0870Theory;
val () = new_theory "vfmTest0870";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0870") $ get_result_defs "vfmTestDefs0870";
val () = export_theory_no_docs ();
