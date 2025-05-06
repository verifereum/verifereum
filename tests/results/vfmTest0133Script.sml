open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0133Theory;
val () = new_theory "vfmTest0133";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0133") $ get_result_defs "vfmTestDefs0133";
val () = export_theory_no_docs ();
