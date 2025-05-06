open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0815Theory;
val () = new_theory "vfmTest0815";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0815") $ get_result_defs "vfmTestDefs0815";
val () = export_theory_no_docs ();
