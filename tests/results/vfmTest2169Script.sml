Theory vfmTest2169[no_sig_docs]
Ancestors vfmTestDefs2169
Libs wordsLib vfmTestAuxLib vfmTestResultLib
val () = holbuild_extra_outputs ["result2169_0.nsv", "result2169_1.nsv", "result2169_2.nsv", "result2169_3.nsv", "result2169_4.nsv", "result2169_5.nsv", "result2169_6.nsv", "result2169_7.nsv", "result2169_8.nsv", "result2169_9.nsv", "result2169_10.nsv", "result2169_11.nsv", "result2169_12.nsv", "result2169_13.nsv", "result2169_14.nsv", "result2169_15.nsv", "result2169_16.nsv", "result2169_17.nsv", "result2169_18.nsv"];
val thyn = "vfmTestDefs2169";
val defs = get_result_defs thyn;
val () = vfmTestLib.remove_nsv_files thyn;
val () = List.app (ignore o save_result_thm thyn) defs;
