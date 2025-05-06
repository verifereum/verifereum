open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0871Theory;
val () = new_theory "vfmTest0871";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0871") $ get_result_defs "vfmTestDefs0871";
val () = export_theory_no_docs ();
