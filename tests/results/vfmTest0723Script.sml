open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0723Theory;
val () = new_theory "vfmTest0723";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0723") $ get_result_defs "vfmTestDefs0723";
val () = export_theory_no_docs ();
