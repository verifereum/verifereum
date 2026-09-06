Theory vfmTest0159[no_sig_docs]
Ancestors vfmTestDefs0159
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result0159_0.nsv", "result0159_1.nsv", "result0159_2.nsv", "result0159_3.nsv"];
val thyn = "vfmTestDefs0159";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
