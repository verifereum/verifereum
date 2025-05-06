open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0918Theory;
val () = new_theory "vfmTest0918";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0918") $ get_result_defs "vfmTestDefs0918";
val () = export_theory_no_docs ();
