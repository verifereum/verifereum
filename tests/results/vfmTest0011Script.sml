open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0011Theory;
val () = new_theory "vfmTest0011";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0011") $ get_result_defs "vfmTestDefs0011";
val () = export_theory_no_docs ();
