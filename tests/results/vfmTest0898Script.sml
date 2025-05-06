open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0898Theory;
val () = new_theory "vfmTest0898";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0898") $ get_result_defs "vfmTestDefs0898";
val () = export_theory_no_docs ();
