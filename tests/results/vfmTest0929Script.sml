open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0929Theory;
val () = new_theory "vfmTest0929";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0929") $ get_result_defs "vfmTestDefs0929";
val () = export_theory_no_docs ();
