open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0813Theory;
val () = new_theory "vfmTest0813";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0813") $ get_result_defs "vfmTestDefs0813";
val () = export_theory_no_docs ();
