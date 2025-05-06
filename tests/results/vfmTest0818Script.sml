open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0818Theory;
val () = new_theory "vfmTest0818";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0818") $ get_result_defs "vfmTestDefs0818";
val () = export_theory_no_docs ();
