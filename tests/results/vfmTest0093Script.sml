open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0093Theory;
val () = new_theory "vfmTest0093";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0093") $ get_result_defs "vfmTestDefs0093";
val () = export_theory_no_docs ();
