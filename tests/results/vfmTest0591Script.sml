Theory vfmTest0591[no_sig_docs]
Ancestors vfmTestDefs0591
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0591_0.nsv", "result0591_1.nsv"];
val thyn = "vfmTestDefs0591";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
