open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0687Theory;
val () = new_theory "vfmTest0687";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0687") $ get_result_defs "vfmTestDefs0687";
val () = export_theory_no_docs ();
