open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0018Theory;
val () = new_theory "vfmTest0018";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0018") $ get_result_defs "vfmTestDefs0018";
val () = export_theory_no_docs ();
