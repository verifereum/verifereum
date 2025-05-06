open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0437Theory;
val () = new_theory "vfmTest0437";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0437") $ get_result_defs "vfmTestDefs0437";
val () = export_theory_no_docs ();
