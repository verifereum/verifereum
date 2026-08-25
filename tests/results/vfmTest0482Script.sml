Theory vfmTest0482[no_sig_docs]
Ancestors vfmTestDefs0482
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0482_0.nsv", "result0482_1.nsv"];
val thyn = "vfmTestDefs0482";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
