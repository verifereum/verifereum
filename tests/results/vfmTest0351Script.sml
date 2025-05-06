open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0351Theory;
val () = new_theory "vfmTest0351";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0351") $ get_result_defs "vfmTestDefs0351";
val () = export_theory_no_docs ();
