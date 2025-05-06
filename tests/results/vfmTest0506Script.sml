open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0506Theory;
val () = new_theory "vfmTest0506";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0506") $ get_result_defs "vfmTestDefs0506";
val () = export_theory_no_docs ();
