open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0552Theory;
val () = new_theory "vfmTest0552";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0552") $ get_result_defs "vfmTestDefs0552";
val () = export_theory_no_docs ();
