open HolKernel vfmTestAuxLib vfmTestResultLib vfmTestDefs0850Theory;
val () = new_theory "vfmTest0850";
val () = List.app (ignore o save_result_thm default_limit "vfmTestDefs0850") $ get_result_defs "vfmTestDefs0850";
val () = export_theory_no_docs ();
