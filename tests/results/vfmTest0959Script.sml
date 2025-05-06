open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0959Theory;
val () = new_theory "vfmTest0959";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0959") $ get_result_defs "vfmTestDefs0959";
val () = export_theory_no_docs ();
