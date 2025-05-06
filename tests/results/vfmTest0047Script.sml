open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0047Theory;
val () = new_theory "vfmTest0047";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0047") $ get_result_defs "vfmTestDefs0047";
val () = export_theory_no_docs ();
