open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0827Theory;
val () = new_theory "vfmTest0827";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0827") $ get_result_defs "vfmTestDefs0827";
val () = export_theory_no_docs ();
