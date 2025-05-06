open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0533Theory;
val () = new_theory "vfmTest0533";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0533") $ get_result_defs "vfmTestDefs0533";
val () = export_theory_no_docs ();
