open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0607Theory;
val () = new_theory "vfmTest0607";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0607") $ get_result_defs "vfmTestDefs0607";
val () = export_theory_no_docs ();
