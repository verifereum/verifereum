open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0226Theory;
val () = new_theory "vfmTest0226";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0226") $ get_result_defs "vfmTestDefs0226";
val () = export_theory_no_docs ();
