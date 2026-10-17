Theory vfmTest2085[no_sig_docs]
Ancestors vfmTestDefs2085
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2085_0.nsv", "result2085_1.nsv", "result2085_2.nsv", "result2085_3.nsv", "result2085_4.nsv", "result2085_5.nsv", "result2085_6.nsv", "result2085_7.nsv", "result2085_8.nsv", "result2085_9.nsv", "result2085_10.nsv", "result2085_11.nsv", "result2085_12.nsv", "result2085_13.nsv", "result2085_14.nsv", "result2085_15.nsv", "result2085_16.nsv", "result2085_17.nsv"];
val thyn = "vfmTestDefs2085";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
