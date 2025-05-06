open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0033Theory;
val () = new_theory "vfmTest0033";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0033") $ get_result_defs "vfmTestDefs0033";
val () = export_theory_no_docs ();
