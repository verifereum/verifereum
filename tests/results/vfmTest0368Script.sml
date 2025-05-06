open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0368Theory;
val () = new_theory "vfmTest0368";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0368") $ get_result_defs "vfmTestDefs0368";
val () = export_theory_no_docs ();
