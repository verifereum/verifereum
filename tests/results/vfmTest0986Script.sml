open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0986Theory;
val () = new_theory "vfmTest0986";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0986") $ get_result_defs "vfmTestDefs0986";
val () = export_theory_no_docs ();
