open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0221Theory;
val () = new_theory "vfmTest0221";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0221") $ get_result_defs "vfmTestDefs0221";
val () = export_theory_no_docs ();
