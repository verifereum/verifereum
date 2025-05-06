open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0646Theory;
val () = new_theory "vfmTest0646";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0646") $ get_result_defs "vfmTestDefs0646";
val () = export_theory_no_docs ();
