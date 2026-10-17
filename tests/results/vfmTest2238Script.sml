Theory vfmTest2238[no_sig_docs]
Ancestors vfmTestDefs2238
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2238_0.nsv", "result2238_1.nsv", "result2238_2.nsv", "result2238_3.nsv", "result2238_4.nsv", "result2238_5.nsv", "result2238_6.nsv", "result2238_7.nsv", "result2238_8.nsv"];
val thyn = "vfmTestDefs2238";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
