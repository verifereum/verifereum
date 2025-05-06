open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0471Theory;
val () = new_theory "vfmTest0471";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0471") $ get_result_defs "vfmTestDefs0471";
val () = export_theory_no_docs ();
