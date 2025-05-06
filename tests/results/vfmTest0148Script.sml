open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0148Theory;
val () = new_theory "vfmTest0148";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0148") $ get_result_defs "vfmTestDefs0148";
val () = export_theory_no_docs ();
