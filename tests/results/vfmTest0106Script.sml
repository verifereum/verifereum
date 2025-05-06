open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0106Theory;
val () = new_theory "vfmTest0106";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0106") $ get_result_defs "vfmTestDefs0106";
val () = export_theory_no_docs ();
