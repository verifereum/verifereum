open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0838Theory;
val () = new_theory "vfmTest0838";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0838") $ get_result_defs "vfmTestDefs0838";
val () = export_theory_no_docs ();
