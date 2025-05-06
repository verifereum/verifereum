open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0750Theory;
val () = new_theory "vfmTest0750";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0750") $ get_result_defs "vfmTestDefs0750";
val () = export_theory_no_docs ();
