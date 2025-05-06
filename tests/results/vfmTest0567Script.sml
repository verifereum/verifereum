open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0567Theory;
val () = new_theory "vfmTest0567";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0567") $ get_result_defs "vfmTestDefs0567";
val () = export_theory_no_docs ();
