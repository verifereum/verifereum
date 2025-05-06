open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0821Theory;
val () = new_theory "vfmTest0821";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0821") $ get_result_defs "vfmTestDefs0821";
val () = export_theory_no_docs ();
