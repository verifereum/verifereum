open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0973Theory;
val () = new_theory "vfmTest0973";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0973") $ get_result_defs "vfmTestDefs0973";
val () = export_theory_no_docs ();
