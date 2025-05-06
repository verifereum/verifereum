open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0397Theory;
val () = new_theory "vfmTest0397";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0397") $ get_result_defs "vfmTestDefs0397";
val () = export_theory_no_docs ();
