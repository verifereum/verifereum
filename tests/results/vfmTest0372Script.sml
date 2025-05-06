open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0372Theory;
val () = new_theory "vfmTest0372";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0372") $ get_result_defs "vfmTestDefs0372";
val () = export_theory_no_docs ();
