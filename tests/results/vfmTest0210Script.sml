open HolKernel wordsLib vfmTestAuxLib vfmTestResultLib vfmTestDefs0210Theory;
val () = new_theory "vfmTest0210";
val thyn = "vfmTestDefs0210";
val defs = get_result_defs thyn;
val () = List.app (ignore o save_result_thm default_limit thyn) defs;
val () = export_theory_no_docs ();
