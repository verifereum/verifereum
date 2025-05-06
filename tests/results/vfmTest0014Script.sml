open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0014Theory;
val () = new_theory "vfmTest0014";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0014") $ get_result_defs "vfmTestDefs0014";
val () = export_theory_no_docs ();
