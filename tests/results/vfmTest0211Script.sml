Theory vfmTest0211[no_sig_docs]
Ancestors vfmTestDefs0211
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0211_0.nsv", "result0211_1.nsv"];
val thyn = "vfmTestDefs0211";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
