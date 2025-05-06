open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0780Theory;
val () = new_theory "vfmTest0780";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0780") $ get_result_defs "vfmTestDefs0780";
val () = export_theory_no_docs ();
