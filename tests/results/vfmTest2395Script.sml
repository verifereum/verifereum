Theory vfmTest2395[no_sig_docs]
Ancestors vfmTestDefs2395
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2395_0.nsv", "result2395_1.nsv", "result2395_2.nsv", "result2395_3.nsv", "result2395_4.nsv", "result2395_5.nsv", "result2395_6.nsv", "result2395_7.nsv", "result2395_8.nsv", "result2395_9.nsv", "result2395_10.nsv", "result2395_11.nsv", "result2395_12.nsv", "result2395_13.nsv", "result2395_14.nsv", "result2395_15.nsv", "result2395_16.nsv", "result2395_17.nsv", "result2395_18.nsv", "result2395_19.nsv"];
val thyn = "vfmTestDefs2395";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
