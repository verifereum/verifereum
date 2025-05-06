open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0426Theory;
val () = new_theory "vfmTest0426";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0426") $ get_result_defs "vfmTestDefs0426";
val () = export_theory_no_docs ();
