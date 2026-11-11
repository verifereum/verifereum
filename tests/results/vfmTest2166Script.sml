Theory vfmTest2166[no_sig_docs]
Ancestors vfmTestDefs2166
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2166_0.nsv", "result2166_1.nsv", "result2166_2.nsv", "result2166_3.nsv", "result2166_4.nsv", "result2166_5.nsv", "result2166_6.nsv", "result2166_7.nsv"];
val thyn = "vfmTestDefs2166";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
