open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0656Theory;
val () = new_theory "vfmTest0656";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0656") $ get_result_defs "vfmTestDefs0656";
val () = export_theory_no_docs ();
