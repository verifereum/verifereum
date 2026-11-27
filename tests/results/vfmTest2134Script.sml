Theory vfmTest2134[no_sig_docs]
Ancestors vfmTestDefs2134
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2134_0.nsv", "result2134_1.nsv", "result2134_2.nsv", "result2134_3.nsv", "result2134_4.nsv", "result2134_5.nsv", "result2134_6.nsv", "result2134_7.nsv", "result2134_8.nsv", "result2134_9.nsv"];
val thyn = "vfmTestDefs2134";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
