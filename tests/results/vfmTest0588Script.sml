open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0588Theory;
val () = new_theory "vfmTest0588";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0588") $ get_result_defs "vfmTestDefs0588";
val () = export_theory_no_docs ();
